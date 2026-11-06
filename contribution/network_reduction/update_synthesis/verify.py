"""Fresh Lean verification, generated-code checks and exact replay for synthesis."""
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

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
CONTRIBUTION = HERE.parent.parent
ROOT = CONTRIBUTION.parent
spec = importlib.util.spec_from_file_location('previous_audit_reader', HERE.parent/'output_updates'/'verify.py')
audit_reader = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit_reader)
import experiment

RESULT = CONTRIBUTION/'results'/'update_synthesis_verification.json'
BUILD = CONTRIBUTION/'.build'/'update_synthesis'


def rel(path):
    return str(Path(path).relative_to(ROOT))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--upstream', type=Path, default=Path.home()/'projects/ppg-lab/external/SAIV_2025_Alsomitra')
    parser.add_argument('--timeout', type=int, default=1200)
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error('Timeout must be positive')
    BUILD.mkdir(parents=True, exist_ok=True)
    for number in itertools.count(1):
        attempt = BUILD/('attempt-%03d' % number)
        try:
            attempt.mkdir()
            break
        except FileExistsError:
            continue
    report = dict(status='RUNNING', attempt=rel(attempt), timestamp_utc=datetime.now(timezone.utc).isoformat(),
                  scope='Exact rational affine updates; minimal coordinate retention relative to seed; fixed certified hidden layers',
                  lean_build={}, negative_compiler_controls={}, fresh_proof_run=True,
                  new_float32_or_onnx_run=False, second_kernel_run=False)
    started = time.monotonic()
    inputs = []
    initial = {}

    def save():
        audit_reader.save_json(attempt/'RESULT.json', report)
        audit_reader.save_json(RESULT, report)

    save()
    try:
        report['audit_reader_controls'] = audit_reader.parser_controls()
        old_sources = audit_reader.check_old_receipt()
        old_output_receipt = CONTRIBUTION/'results/output_update_verification.json'
        old_output = json.loads(old_output_receipt.read_text())
        if old_output['status'] != 'PASS':
            raise ValueError('Output-update receipt is not PASS')
        previous_module = HERE.parent/'output_updates/OutputUpdates.lean'
        if audit_reader.sha(previous_module) != old_output['sources_sha256'][rel(previous_module)]:
            raise ValueError('Output-update proof changed')
        inputs = old_sources + [old_output_receipt, audit_reader.OLD_RECEIPT, previous_module,
                 Path(audit_reader.__file__), HERE.parent/'REPORT.md', HERE.parent/'NETWORK_REDUCTION.pdf',
                 ROOT/'lean/lean-toolchain', ROOT/'lean/lakefile.lean', ROOT/'lean/lake-manifest.json']
        inputs += [p for p in HERE.rglob('*') if p.is_file() and '__pycache__' not in p.parts]
        inputs = sorted(set(inputs))
        initial = {rel(p):audit_reader.sha(p) for p in inputs}
        report['sources_sha256'] = initial
        audit_reader.snapshot_sources(attempt, inputs)
        data = args.upstream/experiment.DATA
        data_hash = audit_reader.sha(data)
        report['calibration_data_sha256'] = data_hash
        (attempt/'Training_Data_Normalised.csv').write_bytes(data.read_bytes())
        generated = attempt/'generated'
        report['experiment'] = experiment.prepare(generated, args.upstream)
        roots = []
        for name in ['AffineRetention','NetworkRetention','RationalFeatures']:
            source = (HERE/(name+'.lean')).read_text()
            ns = re.search(r'^namespace (\S+)$', source, re.M).group(1)
            roots += [ns+'.'+name for name in re.findall(r'^theorem ([A-Za-z_0-9]+)', source, re.M)]
        roots.append('Contribution.Reduction.AffineRetention.stateSetoid')
        roots += report['experiment']['generated_audit_roots']
        audit_source = generated/'Audit.lean'
        audit_source.write_text('import CalibrationBinding\nimport Shifts\nimport Coupling\nimport Chain\n\n'+
                                '\n'.join('#print axioms '+root for root in roots)+'\n')
        expected = audit_reader.expected_roots(audit_source)
        report['expected_roots'] = sorted(expected)
        report['generated_sha256'] = {rel(p):audit_reader.sha(p) for p in sorted(generated.iterdir())}
        pin = (ROOT/'lean/lean-toolchain').read_text().strip()
        if pin != 'leanprover/lean4:v4.35.0':
            raise ValueError('Unexpected Lean toolchain')
        lake = Path.home()/'.elan/toolchains'/pin.replace('/','--').replace(':','---')/'bin/lake'
        report['toolchain'] = pin
        env = os.environ.copy()
        env['LEAN_PATH'] = str(attempt)

        def compile_stage(name, source, negative=False):
            print(('Checking rejection ' if negative else 'Checking ')+name, flush=True)
            out = attempt/(name+'.olean')
            command = [str(lake),'env','lean','-j','1','-R',str(source.parent),'-o',str(out),str(source)]
            tick = time.monotonic()
            proc = subprocess.run(command, cwd=ROOT/'lean', env=env, text=True,
                                  capture_output=True, timeout=args.timeout)
            log = proc.stdout+proc.stderr
            for suffix, text in [('stdout.log',proc.stdout),('stderr.log',proc.stderr),('log',log)]:
                (attempt/(name+'.'+suffix)).write_text(text)
            stage = dict(returncode=proc.returncode, seconds=time.monotonic()-tick,
                         log_sha256=audit_reader.sha(attempt/(name+'.log')),
                         source_sha256=audit_reader.sha(source), command=command)
            if out.exists():
                stage['olean_sha256'] = audit_reader.sha(out)
            target = report['negative_compiler_controls'] if negative else report['lean_build']
            target[name] = stage
            save()
            if negative:
                if proc.returncode == 0 or 'error:' not in log or re.search(r'unknown identifier|unknown module|failed to import',log,re.I):
                    raise RuntimeError('Mutation did not fail at its mathematical obligation: '+name)
                stage['status'] = 'REJECTED'
            elif proc.returncode != 0 or audit_reader.DIAGNOSTIC.search(log) or not out.is_file():
                raise RuntimeError(name+' failed; inspect '+rel(attempt/(name+'.log')))

        stages = [('Property2',CONTRIBUTION/'Property2.lean'),('Float32',CONTRIBUTION/'Float32.lean'),
                  ('IntervalNetwork',CONTRIBUTION/'universal/IntervalNetwork.lean'),
                  ('Pruning',HERE.parent/'Pruning.lean'),('Adversarial',HERE.parent/'Adversarial.lean'),
                  ('OutputUpdates',previous_module)]
        stages += [(name,HERE/(name+'.lean')) for name in ['AffineRetention','NetworkRetention','RationalFeatures']]
        for name, source in stages:
            compile_stage(name, attempt/'sources'/source.relative_to(ROOT))
        for name in ['Shifts','Coupling','Chain','Calibration','CalibrationBinding','Audit']:
            compile_stage(name, generated/(name+'.lean'))
        report['axiom_audit'] = audit_reader.parse_audit((attempt/'Audit.log').read_text(), expected)
        report['audited_roots'] = len(expected)
        original = (generated/'Coupling.lean').read_text()
        bad_mask = original.replace('def kept : Finset (Fin 5) := {0, 1, 2, 4}',
                                    'def kept : Finset (Fin 5) := {0, 2, 4}')
        if original == bad_mask:
            raise ValueError('Mask mutation target missing')
        (generated/'BadMask.lean').write_text(bad_mask)
        compile_stage('BadMask',generated/'BadMask.lean',negative=True)
        lines = original.splitlines()
        for i,line in enumerate(lines):
            if line.startswith('def packedOps '):
                changed = line.replace('(mkRat (1) 1)','(mkRat (2) 1)',1)
                if changed == line:
                    raise ValueError('Packed-matrix mutation target missing')
                lines[i] = changed
                break
        else:
            raise ValueError('Packed operation missing')
        (generated/'BadPacked.lean').write_text('\n'.join(lines)+'\n')
        compile_stage('BadPacked',generated/'BadPacked.lean',negative=True)
        report['generated_sha256'] = {rel(p):audit_reader.sha(p) for p in sorted(generated.iterdir())}
        if audit_reader.sha(data) != data_hash:
            raise RuntimeError('Source CSV changed during verification')
        report['status'] = 'PASS'
    except Exception as exc:
        report['status'] = 'FAIL'
        report['error'] = type(exc).__name__+': '+str(exc)
    finally:
        if initial:
            after = {rel(p):audit_reader.sha(p) for p in inputs}
            report['inputs_unchanged'] = initial == after
            if after != initial:
                report['status'] = 'FAIL'
                report['integrity_error'] = 'Original sources or evidence changed during verification'
        report['seconds'] = time.monotonic()-started
        report['finished_utc'] = datetime.now(timezone.utc).isoformat()
        save()
    print(json.dumps(dict(status=report['status'],audited_roots=report.get('audited_roots',0),
                          attempt=rel(attempt),result=rel(RESULT),error=report.get('error')),indent=2))
    return 0 if report['status']=='PASS' else 1


if __name__ == '__main__':
    raise SystemExit(main())
