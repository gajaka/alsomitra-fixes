"""Fresh kernel replay of the expanded repaired controller and quality gate."""
import argparse
from datetime import datetime, timezone
import hashlib
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
CONTRIBUTION=HERE.parents[1]
ROOT=CONTRIBUTION.parent
NETWORK=CONTRIBUTION/'network_reduction'
HELPER=NETWORK/'output_updates/verify.py'
spec=importlib.util.spec_from_file_location('audit_helpers',HELPER)
helpers=importlib.util.module_from_spec(spec);spec.loader.exec_module(helpers)


def relative(p):return str(p.relative_to(ROOT))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--timeout',type=int,default=1200)
    args=parser.parse_args()
    if args.timeout<=0:parser.error('Positive timeout required')
    base=CONTRIBUTION/'.build/directed_repair';base.mkdir(parents=True,exist_ok=True)
    previous=HERE/'RESULT.json'
    first=1
    if previous.exists():
        recorded=json.loads(previous.read_text()).get('attempt','')
        match=re.search(r'attempt-(\d+)$',recorded)
        if match:first=int(match.group(1))+1
    for n in itertools.count(first):
        attempt=base/f'attempt-{n:03d}'
        try:attempt.mkdir();break
        except FileExistsError:continue
    start=time.monotonic()
    report={'status':'RUNNING','timestamp_utc':datetime.now(timezone.utc).isoformat(),
            'attempt':relative(attempt),'scope':'Expanded core-plus-projection controller: universal Above/Below and exact reference quality',
            'fresh_proof_run':True,'second_kernel_run':False,'architecture_changed':True,
            'lean_build':{},'negative_controls':{}}
    def save():
        helpers.save_json(attempt/'RESULT.json',report)
        helpers.save_json(HERE/'RESULT.json',report)
    save()
    try:
        check=subprocess.run([sys.executable,'-B',str(HERE/'freeze.py'),'--check'],
                             cwd=ROOT,capture_output=True,text=True,timeout=120)
        (attempt/'reconstruction.log').write_text(check.stdout+check.stderr)
        if check.returncode:raise RuntimeError('Frozen artifact reconstruction failed')
        deps=[CONTRIBUTION/'Property2.lean',CONTRIBUTION/'Float32.lean',CONTRIBUTION/'universal/IntervalNetwork.lean']
        deps += [NETWORK/(n+'.lean') for n in ['Pruning','Baseline','Adversarial']]
        deps += [NETWORK/'output_updates/OutputUpdates.lean',NETWORK/'update_synthesis/AffineRetention.lean',
                 NETWORK/'update_synthesis/NetworkRetention.lean',NETWORK/'linear_observations/MomentumQuotient.lean',
                 NETWORK/'update_synthesis/RationalFeatures.lean',NETWORK/'property_transfer/PropertyTransfer.lean',
                 NETWORK/'property_decision/ExactEvaluation.lean']
        own=[HERE/(n+'.lean') for n in ['ProjectionRepair','RepairedCore','RepairNetwork','RepairReference','RepairResult']]
        old_receipts=[CONTRIBUTION/'results'/n for n in ['network_reduction_verification.json','output_update_verification.json',
                      'rmsprop_and_property_transfer_verification.json','property_decision_verification.json']]
        old=[json.loads(p.read_text()) for p in old_receipts]
        if any(r['status']!='PASS' for r in old):raise ValueError('Prior receipt not PASS')
        for p in deps:
            expected=next((r['sources_sha256'][relative(p)] for r in reversed(old) if relative(p) in r['sources_sha256']),None)
            if expected is None or helpers.sha(p)!=expected:raise ValueError('Historical dependency mismatch: '+relative(p))
        csv=HERE.parent/'inputs/Training_Data_Normalised.csv'
        inputs=sorted(set(deps+own+old_receipts+[csv,HELPER,HERE/'CANDIDATE.json',HERE/'FIT.json',
                          HERE/'TRAINING_REPLAY.json',HERE.parent/'prepare_inputs.py']+
                          list(HERE.glob('*.py'))+list(HERE.glob('*.md'))+
                          [ROOT/'lean'/n for n in ['lean-toolchain','lakefile.lean','lake-manifest.json']]))
        initial={relative(p):helpers.sha(p) for p in inputs}
        report['sources_sha256']=initial;helpers.snapshot_sources(attempt,inputs)
        report['candidate']=json.loads((HERE/'CANDIDATE.json').read_text())
        report['reader_controls']=helpers.parser_controls()
        pin=(ROOT/'lean/lean-toolchain').read_text().strip()
        if pin!='leanprover/lean4:v4.35.0':raise ValueError('Unexpected Lean toolchain')
        report['toolchain']=pin
        lake=Path.home()/'.elan/toolchains'/pin.replace('/','--').replace(':','---')/'bin/lake'
        env=os.environ.copy();env['LEAN_PATH']=str(attempt)
        def compile_one(p,negative=False):
            name=p.stem;print(('Rejecting ' if negative else 'Checking ')+name,flush=True)
            out=attempt/(name+'.olean');t=time.monotonic()
            command=[str(lake),'env','lean','-j','1','-R',str(p.parent),'-o',str(out),str(p)]
            proc=subprocess.run(command,cwd=ROOT/'lean',env=env,capture_output=True,text=True,timeout=args.timeout)
            log=proc.stdout+proc.stderr
            for suffix,body in [('log',log),('stdout.log',proc.stdout),('stderr.log',proc.stderr)]:
                (attempt/(name+'.'+suffix)).write_text(body)
            item={'returncode':proc.returncode,'seconds':time.monotonic()-t,'command':command,
                  'source_sha256':helpers.sha(p),'log_sha256':helpers.sha(attempt/(name+'.log'))}
            if out.exists():item['olean_sha256']=helpers.sha(out)
            report['negative_controls' if negative else 'lean_build'][name]=item;save()
            if negative:
                if proc.returncode==0 or not re.search(r'unsolved goals|decide.*(?:failed|evaluated)|evaluated to',log,re.I):
                    raise RuntimeError('Missing mathematical rejection: '+name)
                if re.search(r'unknown identifier|unknown module|failed to import|unexpected token|failed to compile|warning:',log,re.I):
                    raise RuntimeError('Infrastructure error in negative control: '+name)
                item['status']='REJECTED'
            elif proc.returncode or helpers.DIAGNOSTIC.search(log) or not out.exists():
                raise RuntimeError(name+' failed; inspect '+relative(attempt/(name+'.log')))
        for p in deps+own:compile_one(attempt/'sources'/p.relative_to(ROOT))
        gen=attempt/'generated';gen.mkdir()
        roots=['Contribution.DirectedRepair.'+name for p in own for name in re.findall(r'^theorem (\w+)',p.read_text(),re.M)]
        audit=gen/'Audit.lean'
        audit.write_text('import RepairResult\n\n'+'\n'.join('#print axioms '+r for r in roots)+'\n')
        expected=helpers.expected_roots(audit);report['expected_roots']=sorted(expected)
        compile_one(audit)
        report['axiom_audit']=helpers.parse_audit((attempt/'Audit.log').read_text(),expected)
        report['audited_roots']=len(expected)
        controls={
            'ReversedSlope':'''import ProjectionRepair
open Contribution.DirectedRepair
example : (1/2 : ℚ) ≤ projectQ (-64) 3 0 := by decide +kernel
''',
            'OriginalBelowFailure':'''import RepairNetwork
open Contribution.DirectedRepair Contribution.Reduction
set_option maxRecDepth 100000
example : rawQ Adversarial.original [0,0,0,0,0,0] ≤ 1/2 := by decide +kernel
''',
            'ConstantQualityFailure':'''import RepairReference
open Contribution.DirectedRepair
set_option maxRecDepth 100000
set_option maxHeartbeats 0
example : mseQ (fun _ => 1/2) referenceRows < 109/1000 := by decide +kernel
''',
            'BadPruning':'''import RepairedCore
open Contribution.DirectedRepair Contribution.Reduction
set_option maxRecDepth 100000
example : Check fullCore Adversarial.domain
    { pruningCertificate with firstKeep := [false,true,true,false,true,false] } := by decide +kernel
'''}
        for name,body in controls.items():
            p=gen/(name+'.lean');p.write_text(body);compile_one(p,True)
        report['generated_sha256']={relative(p):helpers.sha(p) for p in gen.iterdir()}
        if initial!={relative(p):helpers.sha(p) for p in inputs}:raise ValueError('Input changed during replay')
        report['inputs_unchanged']=True;report['status']='PASS'
    except Exception as exc:
        report['status']='FAIL';report['error']=str(exc)
    finally:
        report['seconds']=time.monotonic()-start;report['finished_utc']=datetime.now(timezone.utc).isoformat();save()
    print(report['status']+': '+relative(HERE/'RESULT.json'),flush=True)
    if report['status']!='PASS':print(report.get('error'),file=sys.stderr);return 1
    return 0


if __name__=='__main__':raise SystemExit(main())
