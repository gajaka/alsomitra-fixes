"""Exact row-space closure with derivation DAGs and Lean-checkable certificates.

Gaussian elimination is an untrusted producer. The proof checker verifies
row generation, closure, independent pivots and the emitted reduced maps.
"""
from fractions import Fraction as Q
import csv
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent/'update_synthesis'))
import synthesize as coordinate
import experiment as previous_experiment


def dot(a,b):
    return sum((x*y for x,y in zip(a,b)),Q(0))


def row_times(row, matrix):
    return [dot(row,col) for col in zip(*matrix)]


def closure(seeds, ops):
    """Return RREF rows, pivots, and an immutable derivation DAG."""
    nodes=[]
    basis={}
    def node(value):
        nodes.append(value)
        return len(nodes)-1
    def subtract(row,d,c,brow,bd):
        return [x-c*y for x,y in zip(row,brow)],node(('add',d,node(('scale',-c,bd))))
    def insert(row,d):
        for p,(brow,bd) in sorted(basis.items()):
            if row[p]:
                row,d=subtract(row,d,row[p],brow,bd)
        if not any(row):
            return False
        p=next(i for i,x in enumerate(row) if x)
        scale=1/row[p]
        row=[scale*x for x in row]
        d=node(('scale',scale,d))
        for bp,(brow,bd) in list(basis.items()):
            if brow[p]:
                basis[bp]=subtract(brow,bd,brow[p],row,d)
        basis[p]=(row,d)
        return True
    for i,row in enumerate(seeds):
        insert(row[:],node(('seed',i)))
    rounds=[]
    while True:
        rounds.append(len(basis))
        added=False
        for row,d in list(basis.values()):
            for k,(matrix,_) in enumerate(ops):
                added=insert(row_times(row,matrix),node(('next',k,d))) or added
        if not added:
            break
    pivots=sorted(basis)
    rows=[basis[p][0] for p in pivots]
    derivations=[basis[p][1] for p in pivots]
    # Retain only nodes reachable from the final proof witnesses.
    needed=set()
    def visit(i):
        if i in needed: return
        needed.add(i)
        tag,*args=nodes[i]
        children=args if tag=='add' else args[1:] if tag in ('scale','next') else []
        for j in children: visit(j)
    for i in derivations: visit(i)
    return rows,pivots,nodes,derivations,sorted(needed),rounds


def momentum_operation(z,target,rate,momentum,penalty):
    d=list(map(Q,[1,1,0,1,0]))
    g=[[z[i]*z[j]+penalty*d[i]*d[j] for j in range(5)] for i in range(5)]
    matrix=[]
    for i in range(5):
        matrix.append([Q(i==j)-rate*g[i][j] for j in range(5)]+
                      [-rate*momentum*Q(i==j) for j in range(5)])
    for i in range(5):
        matrix.append(g[i]+[momentum*Q(i==j) for j in range(5)])
    offset=[rate*target*t for t in z]+[-target*t for t in z]
    return matrix,offset


def matlean(rows):
    return 'Matrix.of '+coordinate.vector([coordinate.vector(list(map(coordinate.qlean,row))) for row in rows])


def emit(name,seeds,ops,config):
    rows,pivots,nodes,ds,needed,rounds=closure(seeds,ops)
    n,p,m,r=len(rows[0]),len(seeds),len(ops),len(rows)
    reduced=[]
    for matrix,offset in ops:
        acted=[row_times(row,matrix) for row in rows]
        small=[[row[j] for j in pivots] for row in acted]
        assert all(row==[sum((a*b[j] for a,b in zip(cs,rows)),Q(0)) for j in range(n)]
                   for row,cs in zip(acted,small))
        reduced.append((small,[dot(row,offset) for row in rows]))
    seed_coeff=[[row[j] for j in pivots] for row in seeds]
    lines=['import LinearObservations','import MomentumQuotient','import CalibrationBinding','',
           'set_option autoImplicit false','set_option maxRecDepth 100000','set_option maxHeartbeats 0',
           'namespace Contribution.Reduction.LinearGenerated.'+name,
           'open AffineRetention LinearObservations','open scoped Matrix',
           f'def seeds : Matrix (Fin {p}) (Fin {n}) ℚ := '+matlean(seeds),
           f'def rows : Matrix (Fin {r}) (Fin {n}) ℚ := '+matlean(rows),
           f'def pivots : Fin {r} → Fin {n} := '+coordinate.vector(list(map(str,pivots))),
           f'def ops : Fin {m} → Affine {n} := '+coordinate.vector([coordinate.affine(op) for op in ops]),
           f'def small : Fin {m} → Affine {r} := '+coordinate.vector([coordinate.affine(op) for op in reduced]),
           f'def seedCoeffs : Matrix (Fin {p}) (Fin {r}) ℚ := '+matlean(seed_coeff)]
    for i in needed:
        tag,*args=nodes[i]
        if tag=='seed': term=f'.seed {args[0]}'
        elif tag=='next': term=f'.next {args[0]} d{args[1]}'
        elif tag=='scale': term=f'.scale {coordinate.qlean(args[0])} d{args[1]}'
        else: term=f'.add d{args[0]} d{args[1]}'
        lines.append(f'def d{i} : Derivation {p} {m} := {term}')
    lines += [f'def derivations : Fin {r} → Derivation {p} {m} := '+coordinate.vector(['d'+str(i) for i in ds]),
        'theorem derivation_values : ∀ i j, rows i j = interpret seeds ops (derivations i) j := by',
        '  intro i j; fin_cases i <;> fin_cases j <;> decide +kernel',
        'theorem derivation_certificate : ∀ i, rows i = interpret seeds ops (derivations i) := by',
        '  intro i; funext j; exact derivation_values i j',
        'theorem pivot_certificate : ∀ i j, rows i (pivots j) = if i = j then 1 else 0 := by decide +kernel',
        'theorem closure_certificate : ∀ k i, pull (ops k) (rows i) =',
        '    ∑ j, (small k).matrix i j • rows j := by decide +kernel',
        'theorem seed_values : ∀ i j, seeds i j = ∑ k, seedCoeffs i k * rows k j := by',
        '  intro i j; fin_cases i <;> fin_cases j <;> decide +kernel',
        'theorem seed_certificate : ∀ i, seeds i = ∑ j, seedCoeffs i j • rows j := by',
        '  intro i; funext j',
        '  simpa [Finset.sum_apply, smul_eq_mul] using seed_values i j',
        'theorem matrix_certificate : ∀ k, rows * matrix (ops k) = matrix (small k) * rows := by decide +kernel',
        'theorem offset_certificate : ∀ k, observe rows (ops k).offset = (small k).offset := by decide +kernel',
        'theorem seed_in_space : ∀ i, seeds i ∈ rowSpace rows := by',
        '  intro i; rw [seed_certificate]; exact combination_mem rows _',
        'theorem invariant : Invariant ops (rowSpace rows) := invariant_of_rows ops rows _ closure_certificate',
        'theorem independent : LinearIndependent ℚ rows := independent_of_pivots rows pivots pivot_certificate',
        f'theorem least (space : Submodule ℚ (Vector {n}))',
        '    (hs : ∀ i, seeds i ∈ space) (hi : Invariant ops space) : rowSpace rows ≤ space :=',
        '  rows_minimal seeds ops rows derivations derivation_certificate space hs hi',
        f'theorem dimension_bound (space : Submodule ℚ (Vector {n}))',
        f'    (hs : ∀ i, seeds i ∈ space) (hi : Invariant ops space) : {r} ≤ Module.finrank ℚ space :=',
        '  dimension_lower_bound seeds ops rows derivations derivation_certificate independent space hs hi',
        f'theorem factors (k : Fin {m}) (x : Vector {n}) :',
        '    observe rows ((ops k).apply x) = (small k).apply (observe rows x) :=',
        '  affine_factors rows (ops k) (small k) (matrix_certificate k) (offset_certificate k) x',
        f'theorem sequences (word : List (Fin {m})) (x : Vector {n}) :',
        '    observe rows (AffineRetention.run ops word x) = AffineRetention.run small word (observe rows x) :=',
        '  sequence_factors rows ops small factors word x',
        'def config : MomentumQuotient.Config := ⟨'+', '.join(map(coordinate.qlean,config))+'⟩',
        'theorem checkpoint_feature_binding : config.z0 = UpdateSynthesis.CalibrationBinding.z 0 ∧',
        '    config.z2 = UpdateSynthesis.CalibrationBinding.z 2 ∧',
        '    config.target = UpdateSynthesis.CalibrationBinding.target := by decide +kernel',
        f'theorem optimizer_binding (x : Vector {n}) : (ops 0).apply x = MomentumQuotient.step config x := by',
        '  funext i',
        '  fin_cases i <;>',
        '    dsimp [ops, Affine.apply, MomentumQuotient.step, MomentumQuotient.velocity,',
        '      MomentumQuotient.gradient, config]',
        '  all_goals norm_num [Fin.sum_univ_succ]',
        '  all_goals ring']
    kept,_=coordinate.retention({0,2,4},ops)
    lines += [f'theorem coordinate_baseline : synthesize ops ({{0,2,4}} : Finset (Fin {n})) = {coordinate.finset(kept)} := by decide +kernel',
              f'theorem retained_dimension : Module.finrank ℚ (rowSpace rows) = {r} := by',
              '  change Module.finrank ℚ (Submodule.span ℚ (Set.range (fun i => rows i))) = _',
              f'  simpa only [Fintype.card_fin] using (finrank_span_eq_card (R := ℚ) (M := Vector {n}) (b := fun i => rows i) independent)']
    pos=[pivots.index(i) for i in [0,2,4]]
    lines += [f'def smallOutput (input : OutputUpdates.Input) (x : Vector {r}) : ℝ :=',
        f'  OutputUpdates.reducedOutput (input,⟨x {pos[0]},x {pos[1]},x {pos[2]}⟩)',
        f'theorem output_factors (input : OutputUpdates.Input) (x : Vector {n}) :',
        '    MomentumQuotient.output input x = smallOutput input (observe rows x) := by',
        f'  have h : ∀ i : Fin 3, observe rows x (![{pos[0]},{pos[1]},{pos[2]}] i) = x (![0,2,4] i) := by',
        '    intro i; fin_cases i <;> norm_num [observe, rows, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]',
        '  unfold smallOutput',
        '  rw [show observe rows x '+str(pos[0])+' = x 0 from h 0,',
        '    show observe rows x '+str(pos[1])+' = x 2 from h 1,',
        '    show observe rows x '+str(pos[2])+' = x 4 from h 2]',
        '  exact OutputUpdates.output_factors (input,MomentumQuotient.head x)',
        f'theorem network_sequences (input : OutputUpdates.Input) (word : List (Fin {m})) (x : Vector {n}) :',
        '    MomentumQuotient.output input (AffineRetention.run ops word x) =',
        '      smallOutput input (AffineRetention.run small word (observe rows x)) := by',
        '  rw [output_factors, sequences]']
    if r==8:
        lines += ['theorem canonical_view (x : Vector 10) : observe rows x = MomentumQuotient.view x := by',
                  '  funext i; fin_cases i <;> norm_num [observe, rows, MomentumQuotient.view, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]',
                  'theorem strict_dimension_gain : 8 < (synthesize ops ({0,2,4} : Finset (Fin 10))).card := by',
                  '  rw [coordinate_baseline]; decide +kernel']
    lines += ['end Contribution.Reduction.LinearGenerated.'+name,'']
    result=dict(full_dimension=n,coordinate_dimension=len(kept),linear_dimension=r,
                closure_dimensions=rounds,pivots=pivots,rows=[[str(x) for x in row] for row in rows],
                derivation_nodes=len(needed),derivations=[
                    [str(x) if isinstance(x,Q) else x for x in nodes[i]] for i in needed])
    return '\n'.join(lines),result,reduced,rows


def prepare(output,upstream):
    output.mkdir(parents=True,exist_ok=True)
    _,witness=previous_experiment.calibration(upstream)
    z=list(map(Q,witness['features']));target=Q(witness['target'])
    seeds=[[Q(i==j) for j in range(10)] for i in [0,2,4]]
    results={}
    for name,penalty in [('Ordinary',Q(0)),('Coupled',Q(1,100))]:
        config=[z[0],z[2],target,Q(1,100),Q(9,10),penalty]
        ops=[momentum_operation(z,target,*config[3:])]
        source,result,small,rows=emit(name,seeds,ops,config)
        (output/(name+'.lean')).write_text(source)
        (output/(name+'.json')).write_text(json.dumps(result,indent=2,default=str)+'\n')
        initial=list(map(Q,witness['initial_head']))+[Q(0)]*5
        # Include arbitrary optimizer memories and the true zero-memory head.
        states=[initial,[Q(0)]*10]+[[Q(i==j) for j in range(10)] for i in range(10)]
        comparisons=0
        for state in states:
            full=state[:];red=[dot(row,state) for row in rows]
            for _ in range(16):
                full=coordinate.apply(ops[0],full);red=coordinate.apply(small[0],red)
                assert red==[dot(row,full) for row in rows]
                comparisons+=1
        result['exact_replay_comparisons']=comparisons
        result['checkpoint_binding']=witness
        results[name]=result
    results['mixed_sequence']=mixed_sequence(upstream,witness)
    return results


def mixed_sequence(upstream,witness):
    source=(HERE.parent/'Adversarial.lean').read_text()
    literal=re.search(r'^def originalRationals : List ℚ := (.*)$',source,re.M).group(1)
    params=[Q(int(a),int(b)) for a,b in re.findall(r'mkRat \((-?\d+)\) (\d+)',literal)]
    with (upstream/previous_experiment.DATA).open() as stream:
        samples=[list(map(Q,row)) for _,row in zip(range(8),csv.reader(stream))]
    features=[]
    for sample in samples:
        x=sample[:6]
        assert all(0<=v<=1 for v in x)
        position=0
        for width,size in [(6,6),(6,4)]:
            w=[params[position+i*width:position+(i+1)*width] for i in range(size)]
            position+=width*size
            b=params[position:position+size];position+=size
            x=[max(Q(0),dot(row,x)+bias) for row,bias in zip(w,b)]
        assert x[1]==x[3]==0
        features.append(x+[Q(1)])
    def view(x): return [x[0],x[1]+x[3],x[2],x[4],x[5],x[6]+x[8],x[7],x[9]]
    full=list(map(Q,witness['initial_head']))+[Q(0)]*5
    small=view(full)
    rate,momentum,penalty=Q(1,100),Q(9,10),Q(1,100)
    checks=0
    for k in list(range(8))*2:
        z,target=features[k],samples[k][6]
        error=dot(full[:5],z)-target
        coupled=penalty*(full[0]+full[1]+full[3])
        grad=[error*z[0]+coupled,coupled,error*z[2],coupled,error]
        v=[momentum*old+g for old,g in zip(full[5:],grad)]
        direct=[a-rate*b for a,b in zip(full[:5],v)]+v
        affine=coordinate.apply(momentum_operation(z,target,rate,momentum,penalty),full)
        assert direct==affine
        e=small[0]*z[0]+small[2]*z[2]+small[3]-target
        g=penalty*(small[0]+small[1])
        rv=[momentum*small[4]+e*z[0]+g,momentum*small[5]+2*g,
            momentum*small[6]+e*z[2],momentum*small[7]+e]
        small=[a-rate*b for a,b in zip(small[:4],rv)]+rv
        full=direct
        assert small==view(full)
        checks+=1
    return dict(physical_csv_rows=list(range(1,9)),passes=2,steps=checks,
                all_direct_affine_and_aggregate_states_equal=True,
                initial_state='Actual checkpoint head and zero momentum',
                final_observed_state=list(map(str,small)),
                scope='Exact arithmetic replay with changing examples; no accuracy or float32 claim')
