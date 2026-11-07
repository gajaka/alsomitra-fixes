"""Freeze the selected fit to dyadic weights and generate exact Lean inputs."""
from fractions import Fraction as F
import argparse
import csv
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
CONTRIBUTION = HERE.parents[1]
SOURCE = HERE/'FIT.json'
CSV = HERE.parent/'inputs/Training_Data_Normalised.csv'


def layers(flat, widths):
    result = []
    offset = 0
    for ins, outs in zip(widths, widths[1:]):
        w = [list(flat[offset+i*ins:offset+(i+1)*ins]) for i in range(outs)]
        offset += ins*outs
        b = list(flat[offset:offset+outs]); offset += outs
        result.append((w, b))
    assert offset == len(flat)
    return result


def evaluate(net, x):
    for w, b in net:
        x = [max(F(0), sum((a*v for a, v in zip(row, x)), bias)) for row, bias in zip(w, b)]
    return x[0]


def displacement(x):
    return (F('41.232296222734604')*x[4]+F('0.482420778264618')
            +F('45.878638794593570')*x[5]-F('41.681405266088724'))


def project(d, z):
    lo = min(F(1,2), max(F(0), F(1,2)+64*(d-2)))
    hi = max(F(1,2), min(F(1), F(1,2)+64*(d+2)))
    return max(lo, min(hi, z))


def rational(x):
    return f'({x.numerator}/{x.denominator} : ℚ)'


def lean_network(name, net):
    layer_text = []
    for w, b in net:
        layer_text.append('['+',\n'.join('⟨['+', '.join(map(rational,row))+'], '+rational(v)+'⟩'
                                         for row,v in zip(w,b))+']')
    return 'def '+name+' : Network := ⟨\n'+',\n'.join(layer_text)+'\n⟩\n'


def interval_layer(net, intervals):
    w,b=net;out=[]
    for row,bias in zip(w,b):
        lo=hi=bias
        for a,(l,u) in zip(row,intervals):
            lo+=min(a*l,a*u);hi+=max(a*l,a*u)
        out.append((lo,hi))
    return out


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    def emit(name,body):
        path=HERE/name
        if args.check:
            if path.read_text()!=body:raise ValueError('Generated artifact differs: '+name)
        else:path.write_text(body)
    assert hashlib.sha256(CSV.read_bytes()).hexdigest() == 'd0b84c0e372a25f7934953ae8adac8db08b7a3b241892a1aa697834f583acbf7'
    if args.check:
        frozen=json.loads((HERE/'CANDIDATE.json').read_text())
        flat=list(map(F,frozen['core_parameters']))
        source_sha=frozen['fit_source_sha256']
        assert frozen['core_widths']==[6,4,2,1] and frozen['slope']=='64'
        assert hashlib.sha256(SOURCE.read_bytes()).hexdigest()==source_sha
        fit=json.loads(SOURCE.read_text())
        assert [F(round(F.from_float(v)*65536),65536) for v in fit['parameters_float64']]==flat
    else:
        source=json.loads(SOURCE.read_text())
        assert source['widths']==[6,4,2,1] and source['k']==64
        flat=[F(round(F.from_float(v)*65536),65536) for v in source['parameters_float64']]
        source_sha=hashlib.sha256(SOURCE.read_bytes()).hexdigest()
    small=layers(flat,[6,4,2,1])
    p=CONTRIBUTION/'network_reduction/Adversarial.lean'
    line=re.search(r'^def originalRationals .*$',p.read_text(),re.M).group()
    original=layers([F(int(a),int(b)) for a,b in re.findall(r'mkRat \((-?\d+)\) (\d+)',line)],[6,6,4,1])
    full=[([list(row) for row in w],list(b)) for w,b in original]
    first_keep=[0,1,2,4];second_keep=[0,2]
    for i,j in enumerate(first_keep):
        full[0][0][j]=list(small[0][0][i]);full[0][1][j]=small[0][1][i]
    for i,j in enumerate(second_keep):
        for u,v in enumerate(first_keep):full[1][0][j][v]=small[1][0][i][u]
        full[1][1][j]=small[1][1][i]
    for i,j in enumerate(second_keep):full[2][0][0][j]=small[2][0][0][i]
    full[2][1][0]=small[2][1][0]
    first=interval_layer(full[0],[(F(0),F(1))]*6)
    second=interval_layer(full[1],[(max(F(0),l),max(F(0),u)) for l,u in first])
    assert first[3][1]<=0 and first[5][1]<=0
    assert second[1][1]<=0 and second[3][1]<=0
    with CSV.open() as f:rows=[[F(x) for x in row] for row in csv.reader(f)]
    assert len(rows)==360 and all(len(r)==7 for r in rows)
    mse=lambda fn:sum((fn(row[:6])-row[6])**2 for row in rows)/len(rows)
    new=mse(lambda x:project(displacement(x),evaluate(small,x)))
    old=mse(lambda x:evaluate(original,x));constant=mse(lambda x:F(1,2))
    assert new<=old and new<constant
    assert new<=F(1476,1000000) and old>=F(1532,1000000) and constant>=F(109,1000)
    for row in rows:assert evaluate(small,row[:6])==evaluate(full,row[:6])
    info={'kind':'expanded architecture: fitted core plus six-ReLU repair block',
          'core_widths':[6,4,2,1],'slope':'64','parameter_denominator':65536,
          'core_parameters':list(map(str,flat)),'fit_source_sha256':source_sha,
          'dataset_sha256':hashlib.sha256(CSV.read_bytes()).hexdigest(),
          'mse_exact':str(new),'mse':float(new),'original_mse_exact':str(old),'original_mse':float(old),
          'constant_mse_exact':str(constant),'constant_mse':float(constant),
          'relative_mse_improvement':float((old-new)/old),
          'scope':'exact rational reference evaluation; Lean proof separately checked'}
    emit('CANDIDATE.json',json.dumps(info,indent=2)+'\n')
    source='''import ProjectionRepair
import ExactEvaluation

/-! Frozen dyadic fit and a fresh pruning certificate for its expanded core.
The output repair block is additional to both full and smaller cores. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Contribution.DirectedRepair
open Contribution.Universal Contribution.Reduction
'''+lean_network('smallCore',small)+lean_network('fullCore',full)
    interval=lambda xs:'['+', '.join('⟨'+rational(l)+', '+rational(u)+'⟩' for l,u in xs)+']'
    source+='''def pruningCertificate : Certificate := {
  firstBounds := '''+interval(first)+'''
  secondBounds := '''+interval(second)+'''
  firstKeep := [true,true,true,false,true,false]
  secondKeep := [true,false,true,false] }

theorem pruning_checked : Check fullCore Adversarial.domain pruningCertificate := by
  decide +kernel
theorem smaller_is_pruned : smallCore =
    prune fullCore pruningCertificate.firstKeep pruningCertificate.secondKeep := by
  decide +kernel
theorem core_equal (xs : List ℝ) (hx : InBox Adversarial.domain xs) :
    eval smallCore xs = eval fullCore xs := by
  rw [smaller_is_pruned]
  exact certified_prune fullCore Adversarial.domain pruningCertificate pruning_checked xs hx

end Contribution.DirectedRepair
'''
    emit('RepairedCore.lean',source)
    body=',\n'.join('  (['+', '.join(map(rational,r[:6]))+'], '+rational(r[6])+')' for r in rows)
    emit('RepairReference.lean','''import RepairNetwork

/-! Exact decimal reference inputs and original labels from the pinned CSV. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace Contribution.DirectedRepair

def referenceRows : List (List ℚ × ℚ) := [
'''+body+''']

theorem reference_count : referenceRows.length = 360 := by decide +kernel
theorem reference_in_cube : ∀ row ∈ referenceRows,
    row.1.length = 6 ∧ ∀ v ∈ row.1, 0 ≤ v ∧ v ≤ 1 := by decide +kernel

theorem repaired_mse_bound : mseQ (repairedQ smallCore) referenceRows ≤ 1476/1000000 := by
  decide +kernel
theorem original_mse_bound : (1532/1000000 : ℚ) ≤
    mseQ (rawQ Contribution.Reduction.Adversarial.original) referenceRows := by
  decide +kernel
theorem constant_mse_bound : (109/1000 : ℚ) ≤ mseQ (fun _ => 1/2) referenceRows := by
  decide +kernel

end Contribution.DirectedRepair
''')
    print(json.dumps({k:info[k] for k in ['mse','original_mse','relative_mse_improvement']},indent=2))


if __name__=='__main__':main()
