"""Check the independent specification compiler experiment.

Kernel proofs and finite rational execution checks are reported separately.
No training, network inference, PPG dependency, or vendor kernel is involved.
"""
from collections import Counter
from datetime import datetime,timezone
from fractions import Fraction as Q
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
BUILD=ROOT/'.build'
RESULTS=ROOT/'results'
LEAN=ROOT.parent/'lean'
MODULES=('RegionSyntax','RegionNormalization','RegionCheck','RegionLoss','RegionAlsomitra','RegionExamples')
ALLOWED={'propext','Classical.choice','Quot.sound'}
AXIOMS=re.compile(r"'([^'\n]+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)")
GENERIC=('flip_correct','atom_flip_correct','cell_append','union_correct','meet_correct','lower_correct',
    'compile_correct','point_roundtrip','normalized_roundtrip','normalized_atom','normalized_formula',
    'normalized_region','normalization_compilation_commute','pipeline_correct','atomCheck_correct',
    'checkRegion_correct','checkNormalized_correct','accept_iff','universal_transport','execution_transport',
    'loss_nonnegative','loss_zero_correct','loss_continuous','normalized_closed_embed','normalized_loss_correct',
    'normalized_loss_checker_agree','strict_boundary_obstruction')
ALSOMITRA=('conjunction_correct','domain_correct','property_formula_correct','property2_pipeline',
    'agrees_with_existing_compiler')
EXAMPLES=('retains_second_component','excludes_open_boundary','excludes_gap','includes_closed_boundaries',
    'hull_changes_membership','closing_boundary_changes_membership','double_normalization_changes_membership',
    'dropping_component_changes_membership','empty_region_rejects_all','strict_hinge_is_not_exact')
EXPECTED={'Contribution.RegionCompiler.'+x for x in GENERIC}
EXPECTED|={'Contribution.RegionCompiler.Alsomitra.'+x for x in ALSOMITRA}
EXPECTED|={'Contribution.RegionCompiler.Examples.'+x for x in EXAMPLES}


def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()


def hashes():
    return {str(p.relative_to(ROOT)):sha(p) for p in sorted([*HERE.glob('*.lean'),*HERE.glob('*.py')])}


def call(name,args,timeout=180):
    env=os.environ.copy()
    env['LEAN_PATH']=str(BUILD)+(os.pathsep+env['LEAN_PATH'] if env.get('LEAN_PATH') else '')
    r=subprocess.run(['lake','env','lean','-j','1',*map(str,args)],cwd=LEAN,env=env,
        text=True,capture_output=True,timeout=timeout)
    log=r.stdout+r.stderr
    # Large finite replay goes under ignored .build; summary and digest are public.
    path=(BUILD if name=='runtime' else RESULTS)/('region_'+name+'.log')
    path.write_text(log)
    if r.returncode or re.search(r'\b(?:warning|error):',log): raise RuntimeError(name+':\n'+log[:8000])
    return log


def audit(log):
    rows=AXIOMS.findall(log);counts=Counter(n for n,_ in rows)
    if set(counts)!=EXPECTED or any(c!=1 for c in counts.values()):raise ValueError('incomplete/duplicate audit')
    out={}
    for name,raw in rows:
        axioms={a.strip() for a in raw.split(',') if a.strip()}
        if not axioms<=ALLOWED:raise ValueError('untrusted axiom: '+name)
        out[name]=sorted(axioms)
    return out


def source_predicate(ast,x):
    op=ast[0]
    if op=='top':return True
    if op=='bot':return False
    if op=='not':return not source_predicate(ast[1],x)
    if op=='and':return source_predicate(ast[1],x) and source_predicate(ast[2],x)
    if op=='or':return source_predicate(ast[1],x) or source_predicate(ast[2],x)
    k=Q(ast[1])
    return {'le':x<=k,'lt':x<k,'ge':x>=k,'gt':x>k}[op]


def replay(log):
    base=[['top'],['bot']]+[[op,str(k)] for op in ('le','lt','ge','gt') for k in (-1,0,1)]
    pairs=[[op,p,q] for p in base for q in base for op in ('and','or')]
    expected=base+[['not',p] for p in base]+pairs+[['not',p] for p in pairs]
    rows=[json.loads(line) for line in log.splitlines()]
    if len(rows)!=len(expected)+1:raise ValueError('missing runtime outputs')
    points=list(map(Q,('-2','-1','-1/2','0','1/2','1','3/2','2','3')))
    normalizers=[(Q(0),Q(1)),(Q(10),Q(10)),(Q(-1),Q(3,2))]
    count=0
    for row,formula in zip(rows[:-1],expected):
        if row['formula']!=formula:raise ValueError('unexpected source formula')
        oracle=[[source_predicate(formula,z*s+o) for z in points] for o,s in normalizers]
        if row['checks']!=oracle:raise ValueError('semantic mismatch: '+repr(formula))
        count+=len(points)*len(normalizers)
    ex=rows[-1]
    if ex['kind']!='disconnected' or ex['checks'] != [True,True,True,False,False,True,True]:
        raise ValueError('boundary demonstration failed')
    count+=7
    return dict(status='PASS',source_formulas=len(expected),normalizers=len(normalizers),
        comparisons=count,oracle='independent Python Fraction source-predicate evaluation',
        raw_sha256=hashlib.sha256(log.encode()).hexdigest(),example=ex)


def dependency():
    receipt=ROOT/'results/float32_verification.json'
    report=json.loads(receipt.read_text())
    if report['status']!='PASS':raise ValueError('unchecked prerequisite Property2')
    keys=('Property2.lean','.build/Property2.olean')
    all_hashes=report['sources_sha256']|report['artifacts_sha256']
    for key in keys:
        if sha(ROOT/key)!=all_hashes[key]:raise ValueError('stale Property2: '+key)
    return {key:all_hashes[key] for key in keys}


def main():
    start=time.monotonic()
    report=dict(status='RUNNING',timestamp_utc=datetime.now(timezone.utc).isoformat(),
        scope='Exact Boolean region compilation and positive affine normalization over ordered fields',
        novelty='NOT_ESTABLISHED; core methodology overlaps Vehicle/LDL',
        network_property_proved=False)
    path=RESULTS/'region_compiler_verification.json'
    path.write_text(json.dumps(report,indent=2)+'\n')
    try:
        report['dependencies_sha256']=dependency()
        auditfile=HERE/'RegionAudit.lean'
        auditfile.write_text('import RegionExamples\nimport RegionAlsomitra\n\n'+
            '\n'.join('#print axioms '+n for n in sorted(EXPECTED))+'\n')
        initial=hashes()
        report['lean_version']=call('version',['--version']).strip()
        if 'version 4.35.0,' not in report['lean_version']:raise ValueError('unexpected Lean version')
        report['mathlib_manifest_sha256']=sha(LEAN/'lake-manifest.json')
        for m in MODULES:
            artifact=BUILD/(m+'.olean');artifact.unlink(missing_ok=True)
            call(m,['-R',HERE,'-o',artifact,HERE/(m+'.lean')])
            print('Kernel-checked '+m,flush=True)
        log=call('audit',['-R',HERE,auditfile]);report['theorems']=audit(log)
        matches=list(AXIOMS.finditer(log))
        for bad in ('',log[:matches[-1].start()],log+matches[0].group(0),log.replace('propext','sorryAx',1)):
            try:audit(bad)
            except ValueError:pass
            else:raise RuntimeError('invalid audit accepted')
        report['audit_negative_controls']=4
        report['runtime']=replay(call('runtime',['-R',HERE,'--run',HERE/'RegionMain.lean']))
        if hashes()!=initial or dependency()!=report['dependencies_sha256']:
            raise RuntimeError('inputs changed during verification')
        report['sources_sha256']=initial
        report['artifacts_sha256']={str((BUILD/(m+'.olean')).relative_to(ROOT)):sha(BUILD/(m+'.olean')) for m in MODULES}
        report['status']='PASS'
        print('PASS:',len(report['theorems']),'audited roots;',report['runtime']['comparisons'],'runtime comparisons',flush=True)
    except Exception as e:
        report.update(status='FAIL',error=str(e));raise
    finally:
        report['elapsed_seconds']=round(time.monotonic()-start,3)
        path.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')


if __name__=='__main__':main()
