"""Check the frozen network's universal certificate with Lean's kernel.

This proves the real network and an explicit bounded-error trace model.
It does not turn sampled kernel-error checks into a universal PyTorch proof.
"""
import argparse
from collections import Counter
from datetime import datetime,timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
BUILD=ROOT/'.build'
LEAN=ROOT.parent/'lean'
RESULTS=ROOT/'results'
sys.path.insert(0,str(ROOT))
from torch_bridge import canonical_hash
from generate import build
from check_execution import run as replay

ALLOWED={'propext','Classical.choice','Quot.sound'}
AXIOMS=re.compile(r"'([^'\n]+)' (?:depends on axioms: \[([^\]\n]*)\]|does not depend on any axioms)")
GENERIC=('enclosed','dot_bounds','neuron_sound','layer_sound','relu_sound','exact_layer_trace',
         'exact_trace','box_upper','leaf_sound','bisect_covers','tree_sound')
FROZEN=('network_shape','root_encloses','epsilon_nonnegative','center_admissible','parameters_bound',
        'parameters_decoded','certificate_checked','cap_lt_half','all_approximate_bound','all_approximate_inputs','all_exact_inputs',
        'pre_in_exactBox','property2_exact','property2_approximate','observed_satisfied','property2_region_nonempty')


def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def source_hashes():
    paths=list(HERE.glob('*.lean'))+list(HERE.glob('*.py'))+[HERE/'model.json',ROOT/'Property2.lean',ROOT/'Float32.lean']
    return {str(p.relative_to(ROOT)):sha(p) for p in sorted(paths)}


def call(args,timeout=900):
    env=os.environ.copy();env['LEAN_PATH']=str(BUILD)+(os.pathsep+env['LEAN_PATH'] if env.get('LEAN_PATH') else '')
    return subprocess.run(['lake','env','lean','-j','1',*args],cwd=LEAN,env=env,text=True,capture_output=True,timeout=timeout)


def clean(name,result):
    text=result.stdout+result.stderr
    (RESULTS/('universal_'+name+'.log')).write_text(text)
    if result.returncode or re.search(r'\b(?:warning|error):',text):raise RuntimeError(name+':\n'+text)
    return text


def audit(log,expected):
    rows=AXIOMS.findall(log);counts=Counter(n for n,_ in rows)
    if set(counts)!=expected or any(v!=1 for v in counts.values()):raise ValueError('incomplete/duplicate axiom audit')
    result={}
    for name,raw in rows:
        axioms={a.strip() for a in raw.split(',') if a.strip()}
        if not axioms<=ALLOWED:raise ValueError('untrusted axiom: '+name+': '+str(axioms))
        result[name]=sorted(axioms)
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--upstream',default='/Users/gajaka/projects/ppg-lab/external/property-driven-ml')
    parser.add_argument('--reuse-build',action='store_true',help='reuse successful kernel builds only when source/dependency/artifact hashes still match')
    args=parser.parse_args()
    RESULTS.mkdir(exist_ok=True);BUILD.mkdir(exist_ok=True)
    report=dict(status='RUNNING',timestamp_utc=datetime.now(timezone.utc).isoformat(),
                scope='All real inputs in fixed Property2 anchor=10 region; exact model and explicit bounded-error traces',
                pytorch_universal_status='NOT_PROVED',trained=False)
    path=RESULTS/'universal_verification.json';path.write_text(json.dumps(report,indent=2)+'\n')
    start=time.monotonic()
    try:
        manifest=json.loads((HERE/'model.json').read_text())
        old=json.loads((RESULTS/'float32_verification.json').read_text())
        if old['status']!='PASS':raise ValueError('bridge verification missing')
        for name,h in old['sources_sha256'].items():
            if sha(ROOT/name)!=h:raise ValueError('bridge source changed: '+name)
        original=old['upstream_integration']['receipt']['payload']
        if canonical_hash(manifest['state'])!=original['state_sha256'] or manifest['state_sha256']!=original['state_sha256']:
            raise ValueError('not the same frozen model as the prior bridge')
        if manifest['normalizer']!=original['normalizer'] or manifest['spec']!=original['spec']:
            raise ValueError('not the same contract/normalizer')
        report['generation']=build(manifest)
        expected={'Contribution.Universal.'+x for x in GENERIC}|{'Contribution.Frozen.'+x for x in FROZEN}
        expected|={'Contribution.Frozen.checked'+str(i) for i in range(report['generation']['leaves'])}
        source=(HERE/'FrozenLeaves.lean').read_text()
        leaf_box=re.search(r'theorem checked0 : CheckLeaf network epsilon cap (box\d+) leaf0',source).group(1)
        negatives={
            'wrong_output_bound':f'CheckLeaf network epsilon cap {leaf_box} {{ leaf0 with third := [⟨0,0⟩] }}',
            'missing_neurons':f'CheckLeaf network epsilon cap {leaf_box} {{ leaf0 with second := [] }}',
            'false_cover':'Encloses (rootBox.take 5 ++ [⟨0,0⟩]) exactBox',
        }
        # Prove the NEGATIONS in the kernel: a generic tactic failure is not evidence of falsity.
        negative_file=HERE/'NegativeControls.lean'
        negative_file.write_text('import FrozenCertificate\nset_option autoImplicit false\n'
                                'set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'
                                'namespace Contribution.Frozen\nopen Contribution.Universal\n\n'+
                                '\n\n'.join('theorem reject_'+name+' : ¬ ('+prop+') := by decide +kernel'
                                            for name,prop in negatives.items())+'\n\nend Contribution.Frozen\n')
        expected|={'Contribution.Frozen.reject_'+name for name in negatives}
        audit_file=HERE/'Audit.lean'
        audit_file.write_text('import Property2Network\nimport NegativeControls\n\n'+'\n'.join('#print axioms '+n for n in sorted(expected))+'\n')
        initial=source_hashes();report['sources_sha256']=initial
        version=clean('version',call(['--version']))
        if 'version 4.35.0,' not in version:raise ValueError('unexpected Lean toolchain')
        report['lean_version']=version.strip()
        modules=('IntervalNetwork','FrozenModel','FrozenLeaves','FrozenCertificate','Property2Network','NegativeControls')
        cache_path=BUILD/'universal_build_cache.json'
        cache=json.loads(cache_path.read_text()) if cache_path.exists() else {}
        dependencies={n:sha(BUILD/(n+'.olean')) for n in ('Property2','Float32')}
        report['builds']={}
        for module in modules:
            artifact=BUILD/(module+'.olean')
            key=dict(source=sha(HERE/(module+'.lean')),dependencies=dict(dependencies),
                     lean=version.strip(),mathlib_manifest=sha(LEAN/'lake-manifest.json'))
            entry=cache.get(module,{})
            reused=args.reuse_build and entry.get('key')==key and artifact.exists() and entry.get('artifact')==sha(artifact)
            if not reused:
                artifact.unlink(missing_ok=True)
                clean('build_'+module,call(['-R',str(HERE),'-o',str(artifact),str(HERE/(module+'.lean'))]))
                cache[module]=dict(key=key,artifact=sha(artifact))
                cache_path.write_text(json.dumps(cache,indent=2,sort_keys=True)+'\n')
            dependencies[module]=sha(artifact)
            report['builds'][module]='matched prior checked build' if reused else 'fresh kernel check'
            print(('Reused checked ' if reused else 'Kernel-checked ')+module,flush=True)
        log=clean('audit',call(['-R',str(HERE),str(audit_file)]))
        report['theorems']=audit(log,expected)
        lines=log.splitlines(keepends=True)
        controls=('', ''.join(lines[:-1]),log+lines[0],log.replace('propext','sorryAx',1))
        for malformed in controls:
            try:audit(malformed,expected)
            except ValueError:pass
            else:raise RuntimeError('bad axiom report accepted')
        report['audit_negative_controls']=len(controls)
        report['invalid_certificates_rejected']={'Contribution.Frozen.reject_'+name:'negation proved in Lean kernel' for name in negatives}
        for name in negatives:
            (RESULTS/('universal_expected_'+name+'.log')).unlink(missing_ok=True)
        report['execution_replay']=replay(manifest,args.upstream)
        if source_hashes()!=initial:raise RuntimeError('sources changed during proof check')
        report['artifacts_sha256']={f'.build/{n}.olean':sha(BUILD/(n+'.olean')) for n in modules}
        report['state_sha256']=manifest['state_sha256']
        report['status']='PASS'
        print('Universal proof PASS:',len(report['theorems']),'audited theorem roots',flush=True)
    except Exception as error:
        report.update(status='FAIL',error=str(error));raise
    finally:
        report['elapsed_seconds']=round(time.monotonic()-start,3)
        path.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')


if __name__=='__main__':main()
