"""Fresh proof audit of linear-observable synthesis and optimizer boundaries."""
import argparse
from datetime import datetime,timezone
import importlib.util
import itertools
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
CONTRIBUTION=HERE.parent.parent
ROOT=CONTRIBUTION.parent
spec=importlib.util.spec_from_file_location('audit_helpers',HERE.parent/'output_updates/verify.py')
helpers=importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
import linear_synthesis

RESULT=CONTRIBUTION/'results/linear_observations_verification.json'
BUILD=CONTRIBUTION/'.build/linear_observations'


def rel(p): return str(Path(p).relative_to(ROOT))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--upstream',type=Path,default=Path.home()/'projects/ppg-lab/external/SAIV_2025_Alsomitra')
    parser.add_argument('--timeout',type=int,default=1200)
    args=parser.parse_args()
    if args.timeout<=0: parser.error('Timeout must be positive')
    BUILD.mkdir(parents=True,exist_ok=True)
    for i in itertools.count(1):
        attempt=BUILD/('attempt-%03d'%i)
        try: attempt.mkdir();break
        except FileExistsError: continue
    report=dict(status='RUNNING',attempt=rel(attempt),timestamp_utc=datetime.now(timezone.utc).isoformat(),
                scope='Exact optimizer-state linear observations; fixed hidden layers; rational momentum and real RMSProp boundary',
                lean_build={},negative_controls={},fresh_proof_run=True,second_kernel_run=False,
                new_float32_or_onnx_run=False)
    started=time.monotonic();inputs=[];initial={}
    def save():
        helpers.save_json(attempt/'RESULT.json',report);helpers.save_json(RESULT,report)
    save()
    try:
        prior_path=CONTRIBUTION/'results/update_synthesis_verification.json'
        prior=json.loads(prior_path.read_text())
        if prior['status']!='PASS': raise ValueError('Previous synthesis proof is not PASS')
        # Preserve all earlier bound sources, including the original report.
        for name,digest in prior['sources_sha256'].items():
            if helpers.sha(ROOT/name)!=digest: raise ValueError('Prior input changed: '+name)
        for name,digest in prior['generated_sha256'].items():
            if helpers.sha(ROOT/name)!=digest: raise ValueError('Prior generated source changed: '+name)
        old_generated=ROOT/prior['attempt']/'generated'
        inputs=[ROOT/name for name in prior['sources_sha256']]+[prior_path]
        inputs += [old_generated/'Calibration.lean',old_generated/'CalibrationBinding.lean']
        inputs += [p for p in HERE.rglob('*') if p.is_file() and '__pycache__' not in p.parts]
        inputs=sorted(set(inputs));initial={rel(p):helpers.sha(p) for p in inputs}
        report['sources_sha256']=initial
        helpers.snapshot_sources(attempt,inputs)
        data=args.upstream/linear_synthesis.previous_experiment.DATA
        report['data_sha256']=helpers.sha(data)
        (attempt/'Training_Data_Normalised.csv').write_bytes(data.read_bytes())
        generated=attempt/'generated'
        report['experiment']=linear_synthesis.prepare(generated,args.upstream)
        own=['LinearObservations','MomentumQuotient','AdaptiveBoundary','GradientTransport']
        roots=[]
        for source in [HERE/(name+'.lean') for name in own]+[generated/'Ordinary.lean',generated/'Coupled.lean']:
            text=source.read_text();ns=re.search(r'^namespace (\S+)$',text,re.M).group(1)
            roots += [ns+'.'+name for name in re.findall(r'^theorem ([A-Za-z_0-9]+)',text,re.M)]
        roots.append('Contribution.Reduction.MomentumQuotient.stateSetoid')
        roots += ['Contribution.Reduction.UpdateSynthesis.CalibrationBinding.'+name for name in
                  ['sample_in_domain','features_match_checkpoint','features_erased','initial_head_bound']]
        audit=generated/'Audit.lean'
        audit.write_text('import Ordinary\nimport Coupled\nimport AdaptiveBoundary\nimport GradientTransport\n\n'+
                         '\n'.join('#print axioms '+name for name in roots)+'\n')
        expected=helpers.expected_roots(audit);report['expected_roots']=sorted(expected)
        report['reader_controls']=helpers.parser_controls()
        pin=(ROOT/'lean/lean-toolchain').read_text().strip()
        if pin!='leanprover/lean4:v4.35.0': raise ValueError('Unexpected toolchain')
        lake=Path.home()/'.elan/toolchains'/pin.replace('/','--').replace(':','---')/'bin/lake'
        report['toolchain']=pin
        env=os.environ.copy();env['LEAN_PATH']=str(attempt)
        def compile_one(name,source,negative=False):
            print(('Checking rejection ' if negative else 'Checking ')+name,flush=True)
            out=attempt/(name+'.olean');tick=time.monotonic()
            cmd=[str(lake),'env','lean','-j','1','-R',str(source.parent),'-o',str(out),str(source)]
            proc=subprocess.run(cmd,cwd=ROOT/'lean',env=env,text=True,capture_output=True,timeout=args.timeout)
            log=proc.stdout+proc.stderr
            for suffix,text in [('log',log),('stdout.log',proc.stdout),('stderr.log',proc.stderr)]:
                (attempt/(name+'.'+suffix)).write_text(text)
            rec=dict(returncode=proc.returncode,seconds=time.monotonic()-tick,command=cmd,
                     source_sha256=helpers.sha(source),log_sha256=helpers.sha(attempt/(name+'.log')))
            if out.exists(): rec['olean_sha256']=helpers.sha(out)
            report['negative_controls' if negative else 'lean_build'][name]=rec;save()
            if negative:
                if proc.returncode==0 or 'error:' not in log or re.search(r'unknown identifier|unknown module|failed to import',log,re.I):
                    raise RuntimeError('Invalid rejection control: '+name)
                rec['status']='REJECTED'
            elif proc.returncode!=0 or helpers.DIAGNOSTIC.search(log) or not out.exists():
                raise RuntimeError(name+' failed; inspect '+rel(attempt/(name+'.log')))
        previous=HERE.parent/'update_synthesis'
        stages=[('Property2',CONTRIBUTION/'Property2.lean'),('Float32',CONTRIBUTION/'Float32.lean'),
                ('IntervalNetwork',CONTRIBUTION/'universal/IntervalNetwork.lean'),
                ('Pruning',HERE.parent/'Pruning.lean'),('Adversarial',HERE.parent/'Adversarial.lean'),
                ('OutputUpdates',HERE.parent/'output_updates/OutputUpdates.lean')]
        stages += [(n,previous/(n+'.lean')) for n in ['AffineRetention','NetworkRetention','RationalFeatures']]
        stages += [(n,old_generated/(n+'.lean')) for n in ['Calibration','CalibrationBinding']]
        stages += [(n,HERE/(n+'.lean')) for n in own]
        for name,source in stages: compile_one(name,attempt/'sources'/source.relative_to(ROOT))
        for name in ['Ordinary','Coupled','Audit']: compile_one(name,generated/(name+'.lean'))
        report['axiom_audit']=helpers.parse_audit((attempt/'Audit.log').read_text(),expected)
        report['audited_roots']=len(expected)
        original=(generated/'Coupled.lean').read_text()
        bad=re.sub(r'^def derivations :.*$', 'def derivations : Fin 8 → Derivation 3 1 := fun _ => .seed 0',original,flags=re.M)
        if bad==original: raise ValueError('Missing derivation mutation target')
        (generated/'BadDerivation.lean').write_text(bad)
        compile_one('BadDerivation',generated/'BadDerivation.lean',True)
        lines=original.splitlines()
        for i,line in enumerate(lines):
            if line.startswith('def small :'):
                match=re.search(r'mkRat \((-?\d+)\) (\d+)',line)
                a,b=map(int,match.groups())
                lines[i]=line[:match.start()]+f'mkRat ({a+b}) {b}'+line[match.end():]
                break
        else: raise ValueError('Missing operator mutation target')
        (generated/'BadOperator.lean').write_text('\n'.join(lines)+'\n')
        compile_one('BadOperator',generated/'BadOperator.lean',True)
        report['generated_sha256']={rel(p):helpers.sha(p) for p in sorted(generated.iterdir())}
        if helpers.sha(data)!=report['data_sha256']: raise RuntimeError('CSV changed during run')
        report['status']='PASS'
    except Exception as exc:
        report['status']='FAIL';report['error']=type(exc).__name__+': '+str(exc)
    finally:
        if initial:
            after={rel(p):helpers.sha(p) for p in inputs}
            report['inputs_unchanged']=after==initial
            if after!=initial: report['status']='FAIL';report['integrity_error']='Input changed during run'
        report['seconds']=time.monotonic()-started;report['finished_utc']=datetime.now(timezone.utc).isoformat();save()
    print(json.dumps(dict(status=report['status'],audited_roots=report.get('audited_roots',0),attempt=rel(attempt),error=report.get('error')),indent=2))
    return 0 if report['status']=='PASS' else 1


if __name__=='__main__': raise SystemExit(main())
