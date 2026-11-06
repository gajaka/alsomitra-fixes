"""Rebuild and audit positive checkpoint properties and their reductions."""
import argparse
from datetime import datetime, timezone
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
NETWORK=HERE.parent
CONTRIBUTION=NETWORK.parent
ROOT=CONTRIBUTION.parent
BUILD=CONTRIBUTION/'.build/positive_property'
RESULT=CONTRIBUTION/'results/positive_property_verification.json'
HELPER=NETWORK/'output_updates/verify.py'
spec=importlib.util.spec_from_file_location('audit_helpers',HELPER)
helpers=importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
import extract
import runtime


def rel(p):
    return str(Path(p).relative_to(ROOT))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--upstream',type=Path,required=True)
    parser.add_argument('--timeout',type=int,default=1200)
    args=parser.parse_args()
    if args.timeout<=0:
        parser.error('Timeout must be positive')
    upstream=args.upstream.absolute()
    BUILD.mkdir(parents=True,exist_ok=True)
    for i in itertools.count(1):
        attempt=BUILD/f'attempt-{i:03d}'
        try:
            attempt.mkdir();break
        except FileExistsError:
            continue
    report={'status':'RUNNING','attempt':rel(attempt),'timestamp_utc':datetime.now(timezone.utc).isoformat(),
            'scope':'Global real sensitivity, all-anchor Property5 on the cube, exact neuron deletion, and transfer for two pinned published DL2/Godel checkpoints',
            'fresh_proof_run':True,'second_kernel_run':False,'lean_build':{},'negative_controls':{}}
    started=time.monotonic()

    def save():
        helpers.save_json(attempt/'RESULT.json',report)
        helpers.save_json(RESULT,report)

    save()
    try:
        receipt_names=['network_reduction_verification','output_update_verification','update_synthesis_verification',
            'linear_observations_verification','rmsprop_and_property_transfer_verification','property_decision_verification']
        receipts=[CONTRIBUTION/'results'/(n+'.json') for n in receipt_names]
        old=[json.loads(p.read_text()) for p in receipts]
        if any(r['status']!='PASS' for r in old):
            raise ValueError('Historical receipt not PASS')
        deps=[CONTRIBUTION/'Property2.lean',CONTRIBUTION/'Float32.lean',
              CONTRIBUTION/'universal/IntervalNetwork.lean',NETWORK/'Pruning.lean']
        for p in deps:
            if helpers.sha(p)!=old[-1]['sources_sha256'][rel(p)]:
                raise ValueError('Historical proof changed: '+rel(p))
        own=[HERE/(n+'.lean') for n in ['Lipschitz','LinearPruning','DL2Checkpoint','GodelCheckpoint']]
        config=[ROOT/'lean'/n for n in ['lean-toolchain','lakefile.lean','lake-manifest.json']]
        inputs=sorted(set(deps+own+config+receipts+[HELPER,HERE/'README.md']+list(HERE.glob('*.py'))))
        initial={rel(p):helpers.sha(p) for p in inputs}
        report['sources_sha256']=initial
        report['historical_receipts_sha256']={rel(p):helpers.sha(p) for p in receipts}
        helpers.snapshot_sources(attempt,inputs)
        generated=attempt/'generated'
        report['extraction']=extract.generate(upstream,generated)
        for name in extract.MODELS:
            if (generated/(name+'Checkpoint.lean')).read_bytes()!=(HERE/(name+'Checkpoint.lean')).read_bytes():
                raise ValueError('Generated Lean differs: '+name)
        for rec in report['extraction']['sources']+list(report['extraction']['models'].values()):
            p=upstream/rec['path'];target=attempt/'upstream'/rec['path']
            target.parent.mkdir(parents=True,exist_ok=True)
            target.write_bytes(p.read_bytes())
        roots=[]
        for p in own:
            namespace=re.search(r'^namespace (\S+)',p.read_text(),re.M).group(1)
            roots += [namespace+'.'+n for n in re.findall(r'^theorem (\w+)',p.read_text(),re.M)]
        roots += ['Contribution.Reduction.dot_select','Contribution.Reduction.layer_trim',
                  'Contribution.Reduction.zeros_of_bounds','Contribution.Universal.layer_sound',
                  'Contribution.Float32.decode_none_iff']
        audit=generated/'Audit.lean'
        audit.write_text('import DL2Checkpoint\nimport GodelCheckpoint\n\n'+'\n'.join('#print axioms '+r for r in roots)+'\n')
        expected=helpers.expected_roots(audit)
        report['expected_roots']=sorted(expected)
        report['reader_controls']=helpers.parser_controls()
        pin=(ROOT/'lean/lean-toolchain').read_text().strip()
        if pin!='leanprover/lean4:v4.35.0':
            raise ValueError('Unexpected Lean toolchain')
        lake=Path.home()/'.elan/toolchains'/pin.replace('/','--').replace(':','---')/'bin/lake'
        report['toolchain']=pin
        env=os.environ.copy();env['LEAN_PATH']=str(attempt)

        def compile_one(source,negative=False):
            name=source.stem
            print(('Rejecting ' if negative else 'Checking ')+name,flush=True)
            out=attempt/(name+'.olean')
            command=[str(lake),'env','lean','-j','1','-R',str(source.parent),'-o',str(out),str(source)]
            tick=time.monotonic()
            p=subprocess.run(command,cwd=ROOT/'lean',env=env,capture_output=True,text=True,timeout=args.timeout)
            log=p.stdout+p.stderr
            for suffix,body in [('log',log),('stdout.log',p.stdout),('stderr.log',p.stderr)]:
                (attempt/(name+'.'+suffix)).write_text(body)
            rec={'returncode':p.returncode,'seconds':time.monotonic()-tick,'command':command,
                 'source_sha256':helpers.sha(source),'log_sha256':helpers.sha(attempt/(name+'.log'))}
            if out.exists():
                rec['olean_sha256']=helpers.sha(out)
            report['negative_controls' if negative else 'lean_build'][name]=rec
            save()
            if negative:
                if p.returncode==0 or 'error:' not in log or re.search(r'unknown identifier|unknown module|failed to import|unexpected token',log,re.I):
                    raise RuntimeError('Invalid negative control '+name)
                if not re.search(r'unsolved goals|decide.*(?:failed|evaluated)|evaluated to',log,re.I):
                    raise RuntimeError('Missing mathematical rejection '+name)
                rec['status']='REJECTED'
            elif p.returncode!=0 or helpers.DIAGNOSTIC.search(log) or not out.exists():
                raise RuntimeError('Proof failure: '+rel(attempt/(name+'.log')))

        for p in deps+own:
            compile_one(attempt/'sources'/p.relative_to(ROOT))
        compile_one(audit)
        report['axiom_audit']=helpers.parse_audit((attempt/'Audit.log').read_text(),expected)
        report['audited_roots']=len(expected)
        bad_bound=generated/'BadBound.lean'
        bad_bound.write_text('import DL2Checkpoint\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'+
            'example : Contribution.PositiveProperty.Check Contribution.PositiveProperty.DL2.network 0 := by decide +kernel\n')
        bad_prune=generated/'BadPrune.lean'
        bad_prune.write_text('import GodelCheckpoint\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n'+
            'open Contribution.PositiveProperty\nexample : Contribution.Reduction.Check Godel.network cube\n'+
            '  { Godel.certificate with firstKeep := List.replicate 64 false } := by decide +kernel\n')
        compile_one(bad_bound,True)
        compile_one(bad_prune,True)
        # Exercise the graph bridge against a meaningful altered operator.
        import onnx
        from onnx import helper
        model=onnx.load(upstream/report['extraction']['models']['DL2']['path'])
        attrs=model.graph.node[0].attribute
        for a in attrs:
            if a.name=='transB':
                a.CopyFrom(helper.make_attribute('transB',0))
        mutated=generated/'WrongTranspose.onnx';onnx.save(model,mutated)
        try:
            extract.inspect_model(mutated)
        except Exception as exc:
            report['negative_controls']['WrongTranspose']={'status':'REJECTED','reason':str(exc)}
        else:
            raise ValueError('Wrong transpose accepted')
        print('Checking finite ONNX executions',flush=True)
        report['runtime']=runtime.run(upstream,generated)
        helpers.save_json(attempt/'RUNTIME.json',report['runtime'])
        report['runtime_sha256']=helpers.sha(attempt/'RUNTIME.json')
        report['generated_sha256']={rel(p):helpers.sha(p) for p in generated.iterdir() if p.is_file()}
        if initial!={rel(p):helpers.sha(p) for p in inputs}:
            raise ValueError('Input changed during verification')
        for rec in report['extraction']['sources']+list(report['extraction']['models'].values()):
            if extract.sha(upstream/rec['path'])!=rec['sha256']:
                raise ValueError('Upstream input changed during verification')
        report['inputs_unchanged']=True
        report['status']='PASS'
    except Exception as exc:
        report['status']='FAIL';report['error']=str(exc)
    finally:
        report['seconds']=time.monotonic()-started
        report['finished_utc']=datetime.now(timezone.utc).isoformat();save()
    print(report['status']+': '+rel(RESULT),flush=True)
    if report['status']!='PASS':
        print(report.get('error'),file=sys.stderr)
        return 1
    return 0


if __name__=='__main__':
    raise SystemExit(main())
