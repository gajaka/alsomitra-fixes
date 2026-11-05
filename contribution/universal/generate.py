"""Freeze the previously executed model and generate an exact interval proof.

Python proposes certificates. Lean checks every inequality and the split cover.
No weights, thresholds, or trained checkpoint are changed by this generator.
"""
from fractions import Fraction as Q
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
import time

import torch

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0,str(ROOT))
from torch_bridge import (LeanClient, Spec, canonical_hash, exact_word, request_base,
                          upstream_normalizer, words)

EPS, CAP, TARGET, GRID = Q(1,1024), Q(1,2), Q(49,100), 2**20
PIN = '616df1e5baaabf7b42dc26320c00fb297903c87a'


def save(path, data):
    path.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')


def freeze(upstream):
    manifest = HERE/'model.json'
    if manifest.exists():
        return json.loads(manifest.read_text())
    receipt = json.loads((ROOT/'results/float32_verification.json').read_text())
    payload = receipt['upstream_integration']['receipt']['payload']
    source = Path(upstream)/'examples/models.py'
    if hashlib.sha256(source.read_bytes()).hexdigest() != payload['sources_sha256']['examples/models.py']:
        raise ValueError('upstream model source differs from the executed bridge model')
    module_spec = importlib.util.spec_from_file_location('frozen_original_alsomitra',source)
    module = importlib.util.module_from_spec(module_spec);module_spec.loader.exec_module(module)
    with torch.random.fork_rng(devices=[]):
        torch.manual_seed(payload['initialization_seed'])
        model = module.AlsomitraNet().cpu().float().eval()
    state = {name:dict(shape=list(v.shape),words=words(v)) for name,v in model.state_dict().items()}
    if canonical_hash(state) != payload['state_sha256']:
        raise ValueError('weights do not match the previous bridge observation')
    spec,normalizer = Spec(),upstream_normalizer()
    with LeanClient() as client:
        bounds=client.request(dict(request_base(spec,normalizer),action='bounds'))
    if not bounds['nonempty']:
        raise ValueError('empty verification region')
    result=dict(state=state,state_sha256=canonical_hash(state),original_source_sha256=payload['sources_sha256'],
                upstream_revision=PIN,initialization_seed=payload['initialization_seed'],trained=False,
                spec=spec.fields(),normalizer=normalizer.fields(),exact_bounds=bounds,
                torch_version=torch.__version__,architecture=[6,64,32,1])
    save(manifest,result)
    return result


def layers_from_manifest(manifest):
    result=[]
    for name,width in [('fc1',6),('fc2',64),('fc3',32)]:
        w=list(map(exact_word,manifest['state'][name+'.weight']['words']))
        b=list(map(exact_word,manifest['state'][name+'.bias']['words']))
        if len(w)!=width*len(b):raise ValueError('shape mismatch')
        result.append([(w[i*width:(i+1)*width],v) for i,v in enumerate(b)])
    return result


def floor_grid(q):return Q((q*GRID).__floor__(),GRID)
def ceil_grid(q):return Q((q*GRID).__ceil__(),GRID)


def propagate(layers,box):
    certificates=[]
    for index,layer in enumerate(layers):
        out=[]
        for weights,bias in layer:
            lo=bias-EPS;hi=bias+EPS
            for w,(a,b) in zip(weights,box):
                lo+=w*(a if w>=0 else b);hi+=w*(b if w>=0 else a)
            out.append((floor_grid(lo),ceil_grid(hi)))
        certificates.append(out)
        box=[(max(0,a),max(0,b)) for a,b in out] if index<2 else out
    return certificates


def qlean(q):
    q=Q(q)
    return f'(mkRat ({q.numerator}) {q.denominator})'


def intervals(bs):return '['+', '.join('⟨'+qlean(a)+', '+qlean(b)+'⟩' for a,b in bs)+']'


def build(manifest):
    start=time.monotonic()
    if canonical_hash(manifest['state'])!=manifest['state_sha256']:raise ValueError('model hash mismatch')
    layers=layers_from_manifest(manifest)
    bounds=manifest['exact_bounds']
    exact=list(zip(map(Q,bounds['normalized_lo']),map(Q,bounds['normalized_hi'])))
    root=[(floor_grid(lo),ceil_grid(hi)) for lo,hi in exact]
    nodes=[];leaves=[]
    def visit(box,depth=0):
        index=len(nodes);node=dict(index=index,box=box);nodes.append(node)
        cert=propagate(layers,box)
        if cert[2][0][1]<=TARGET:
            node['leaf']=len(leaves);node['certificate']=cert;leaves.append(node)
        else:
            if depth>=16:raise RuntimeError('no certificate within the declared depth bound')
            axis=max(range(6),key=lambda i:box[i][1]-box[i][0]);cut=sum(box[axis])/2
            left=list(box);right=list(box);left[axis]=(box[axis][0],cut);right[axis]=(cut,box[axis][1])
            node.update(axis=axis,cut=cut,left=visit(left,depth+1),right=visit(right,depth+1))
        return index
    visit(root)
    certified_cap=max(n['certificate'][2][0][1] for n in leaves)
    out=['import IntervalNetwork','import Float32','open Contribution.Property2','namespace Contribution.Frozen',
         'open Contribution.Universal','set_option maxRecDepth 100000','set_option maxHeartbeats 0']
    for name,layer in zip(('first','second','third'),layers):
        neurons=['⟨['+', '.join(map(qlean,ws))+'], '+qlean(b)+'⟩' for ws,b in layer]
        out.append('def '+name+' : List Neuron := [\n'+',\n'.join(neurons)+'\n]')
    out+=['def network : Network := ⟨first,second,third⟩',f'def epsilon : ℚ := {qlean(EPS)}',
          f'def cap : ℚ := {qlean(certified_cap)}',f'def rootBox : List Interval := {intervals(root)}',
          'theorem cap_lt_half : cap < (1/2 : ℚ) := by norm_num [cap]']
    out+=['theorem network_shape : first.length = 64 ∧ second.length = 32 ∧ third.length = 1 ∧\n'
          '    (∀ n ∈ first, n.weights.length = 6) ∧ (∀ n ∈ second, n.weights.length = 64) ∧\n'
          '    (∀ n ∈ third, n.weights.length = 32) := by decide +kernel']
    os=list(map(exact_word,manifest['normalizer']['offset_bits']));ss=list(map(exact_word,manifest['normalizer']['scale_bits']))
    coords=['vx','vy','omega','theta','x','y']
    for name,values in [('offset',os),('scale',ss)]:
        out.append('def '+name+' : Coord → ℚ\n'+ '\n'.join('  | .'+c+' => '+qlean(v) for c,v in zip(coords,values)))
    out+=['def normalizer : Normalizer := ⟨offset,scale,by intro c; cases c <;> norm_num [scale]⟩',
          'def spec : Spec := ⟨10,2,-3/10,-3/25⟩',
          'def exactBox : List Interval :=\n  let b := normalizeBox normalizer (compile spec)\n  ['+
          ', '.join('⟨b.lo.val .'+c+', b.hi.val .'+c+'⟩' for c in coords)+']',
          'theorem root_encloses : Encloses rootBox exactBox := by decide +kernel',
          'theorem epsilon_nonnegative : 0 ≤ epsilon := by norm_num [epsilon]']
    out+=['def center : Normalized := ⟨fun c => match c with\n'+
          '\n'.join('  | .'+c+' => '+qlean((a+b)/2) for c,(a,b) in zip(coords,exact))+'⟩',
          'theorem center_admissible : Pre spec (denormalize normalizer center) := by decide +kernel']
    allbits=[];allq=[]
    for name in ('fc1','fc2','fc3'):
        for suffix in ('weight','bias'):
            bs=manifest['state'][name+'.'+suffix]['words'];allbits+=bs;allq+=list(map(exact_word,bs))
    # Bind the decoded finite parameter words to all rational parameter values.
    out+=['def parameterBits : List Nat := ['+', '.join(map(str,allbits))+']',
          'def parameterRationals : List ℚ := '+ '['+', '.join(map(qlean,allq))+']',
          'def flattenLayer (ns : List Neuron) : List ℚ := ns.flatMap Neuron.weights ++ ns.map Neuron.bias',
          'theorem parameters_bound : flattenLayer first ++ flattenLayer second ++ flattenLayer third = parameterRationals := by rfl',
          'theorem parameters_decoded : parameterBits.map Contribution.Float32.decode = parameterRationals.map some := by decide +kernel',
          'end Contribution.Frozen']
    (HERE/'FrozenModel.lean').write_text('\n\n'.join(out)+'\n')
    lines=['import FrozenModel','namespace Contribution.Frozen','open Contribution.Universal',
           'set_option maxRecDepth 100000','set_option maxHeartbeats 0','def box0 := rootBox']
    for node in nodes:
        if 'leaf' not in node:
            for child,side in [(node['left'],1),(node['right'],2)]:
                lines.append(f"def box{child} := (bisect box{node['index']} {node['axis']} {qlean(node['cut'])}).{side}")
    boxes='\n\n'.join(lines)+'\n'
    proofs=[]
    for node in leaves:
        i=node['leaf'];c=node['certificate']
        proofs += [f'def leaf{i} : Leaf := ⟨'+',\n'.join(map(intervals,c))+'⟩',
                   f'theorem checked{i} : CheckLeaf network epsilon cap box{node["index"]} leaf{i} := by decide +kernel']
    def tree(i):
        n=nodes[i]
        return f'.leaf leaf{n["leaf"]}' if 'leaf' in n else f'.split {n["axis"]} {qlean(n["cut"])} ({tree(n["left"])}) ({tree(n["right"])})'
    def proof(i):
        n=nodes[i]
        return 'checked'+str(n['leaf']) if 'leaf' in n else f'⟨{proof(n["left"])}, {proof(n["right"])}⟩'
    aggregate=[f'def certificate : Tree := {tree(0)}',
               f'theorem certificate_checked : CheckTree network epsilon cap rootBox certificate := {proof(0)}',
               'theorem all_approximate_bound (xs ys : List ℝ) (hx : InBox exactBox xs)\n'
               '    (ht : Trace network epsilon xs ys) : ∀ y ∈ ys, y ≤ (cap : ℝ) := by\n'
               '  exact tree_sound network epsilon cap rootBox certificate certificate_checked xs ys\n'
               '    (enclosed rootBox exactBox xs root_encloses hx) ht',
               'theorem all_approximate_inputs (xs ys : List ℝ) (hx : InBox exactBox xs)\n'
               '    (ht : Trace network epsilon xs ys) : ∀ y ∈ ys, y ≤ (1/2 : ℝ) := by\n'
               '  intro y hy\n'
               '  have hcap : (cap : ℝ) ≤ (1/2 : ℝ) := by norm_num [cap]\n'
               '  exact (all_approximate_bound xs ys hx ht y hy).trans hcap',
               'theorem all_exact_inputs (xs : List ℝ) (hx : InBox exactBox xs) :\n'
               '    ∀ y ∈ network.eval xs, y ≤ (1/2 : ℝ) :=\n'
               '  all_approximate_inputs xs _ hx (exact_trace network epsilon epsilon_nonnegative xs)',
               'end Contribution.Frozen']
    (HERE/'FrozenLeaves.lean').write_text(boxes+'\n\n'.join(proofs+aggregate[:2])+ '\nend Contribution.Frozen\n')
    (HERE/'FrozenCertificate.lean').write_text('import FrozenLeaves\nnamespace Contribution.Frozen\nopen Contribution.Universal\n\n'+
                                             '\n\n'.join(aggregate[2:])+'\n')
    (ROOT/'.build/FirstLeaf.lean').write_text(boxes+'\n\n'.join(proofs[:2])+'\nend Contribution.Frozen\n')
    report=dict(nodes=len(nodes),leaves=len(leaves),epsilon=str(EPS),cap=str(CAP),target=str(TARGET),
                input_box=[[str(a),str(b)] for a,b in exact],cover_box=[[str(a),str(b)] for a,b in root],
                worst_output_upper=str(max(n['certificate'][2][0][1] for n in leaves)),
                generation_seconds=round(time.monotonic()-start,3),state_sha256=manifest['state_sha256'],
                status='GENERATED_NOT_YET_PROVED')
    save(HERE/'generation.json',report)
    print(json.dumps(report,indent=2),flush=True)
    return report


if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('--upstream',default='/Users/gajaka/projects/ppg-lab/external/property-driven-ml')
    args=p.parse_args();build(freeze(args.upstream))
