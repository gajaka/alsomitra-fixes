"""Fresh proof audit of concrete controller-property refutations."""
import argparse
from datetime import datetime, timezone
from fractions import Fraction as F
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
NETWORK = HERE.parent
CONTRIBUTION = NETWORK.parent
ROOT = CONTRIBUTION.parent
BUILD = CONTRIBUTION / '.build/property_decision'
RESULT = CONTRIBUTION / 'results/property_decision_verification.json'
HELPER = NETWORK / 'output_updates/verify.py'
spec = importlib.util.spec_from_file_location('audit_helpers', HELPER)
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
import search


def rel(p):
    return str(Path(p).relative_to(ROOT))


def leanq(value):
    q = F(value)
    return f'({q.numerator}/{q.denominator} : ℚ)'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--timeout', type=int, default=1200)
    parser.add_argument('--runtime-python', type=Path)
    parser.add_argument('--upstream', type=Path)
    args = parser.parse_args()
    if args.timeout <= 0 or bool(args.runtime_python) != bool(args.upstream):
        parser.error('Positive timeout; runtime-python and upstream must be supplied together')
    BUILD.mkdir(parents=True, exist_ok=True)
    for number in itertools.count(1):
        attempt = BUILD / ('attempt-%03d' % number)
        try:
            attempt.mkdir()
            break
        except FileExistsError:
            continue
    report = dict(status='RUNNING', attempt=rel(attempt),
                  timestamp_utc=datetime.now(timezone.utc).isoformat(),
                  scope='Exact real counterexamples to Above(2)/Below(2), two original trained checkpoints and certified reductions',
                  fresh_proof_run=True, second_kernel_run=False, lean_build={}, negative_controls={})
    started = time.monotonic()

    def save():
        helpers.save_json(attempt / 'RESULT.json', report)
        helpers.save_json(RESULT, report)

    save()
    try:
        receipts = [CONTRIBUTION / 'results' / name for name in [
            'network_reduction_verification.json', 'output_update_verification.json',
            'update_synthesis_verification.json', 'linear_observations_verification.json',
            'rmsprop_and_property_transfer_verification.json']]
        previous = [json.loads(p.read_text()) for p in receipts]
        if any(r['status'] != 'PASS' for r in previous):
            raise ValueError('All previous proof receipts must pass')
        deps = [CONTRIBUTION / 'Property2.lean', CONTRIBUTION / 'Float32.lean',
                CONTRIBUTION / 'universal/IntervalNetwork.lean']
        deps += [NETWORK / (n + '.lean') for n in ['Pruning', 'Baseline', 'Adversarial']]
        deps += [NETWORK / 'output_updates/OutputUpdates.lean']
        deps += [NETWORK / 'update_synthesis' / (n + '.lean') for n in ['AffineRetention', 'NetworkRetention']]
        deps += [NETWORK / 'linear_observations/MomentumQuotient.lean',
                 NETWORK / 'property_transfer/PropertyTransfer.lean',
                 NETWORK / 'update_synthesis/RationalFeatures.lean']
        for path in deps:
            expected = previous[-1]['sources_sha256'].get(rel(path),
                       previous[-2]['sources_sha256'].get(rel(path)))
            if helpers.sha(path) != expected:
                raise ValueError('Historical dependency changed: ' + rel(path))
        own = [HERE / 'ExactEvaluation.lean', HERE / 'Witnesses.lean']
        config = [ROOT / 'lean' / n for n in ['lean-toolchain', 'lakefile.lean', 'lake-manifest.json']]
        inputs = sorted(set(deps + own + config + receipts + [HELPER] + list(HERE.glob('*.py')) + [HERE / 'README.md']))
        initial = {rel(p): helpers.sha(p) for p in inputs}
        report['sources_sha256'] = initial
        report['historical_receipts_sha256'] = {rel(p): helpers.sha(p) for p in receipts}
        helpers.snapshot_sources(attempt, inputs)
        found = search.search()
        helpers.save_json(attempt / 'SEARCH.json', found)
        report['search'] = found
        generated = attempt / 'generated'
        generated.mkdir()
        ns = 'Contribution.Reduction.PropertyDecision'
        binding = generated / 'SearchBinding.lean'
        lines = ['import Witnesses', '', 'namespace ' + ns]
        for model, rec in found['models'].items():
            for label, witness in rec['witnesses'].items():
                point = '[' + ','.join(map(leanq, witness['input'])) + ']'
                name = model.lower() + '_' + label.lower()
                lines += [f'theorem {name}_search_binding : evalQ {model}.original {point} =',
                          f'    [{leanq(witness["output_exact"])}] := {name}_computed']
        lines += ['end ' + ns]
        binding.write_text('\n'.join(lines)+'\n')
        roots = []
        for path in own + [binding]:
            roots += [ns + '.' + n for n in re.findall(r'^theorem (\w+)', path.read_text(), re.M)]
        roots += ['Contribution.Reduction.' + m + '.' + n
                  for m in ['Baseline', 'Adversarial']
                  for n in ['original_decoded', 'original_parameters', 'all_real_inputs']]
        roots += ['Contribution.Reduction.PropertyTransfer.' + m + '_counterexample'
                  for m in ['baseline', 'adversarial']]
        audit = generated / 'Audit.lean'
        audit.write_text('import SearchBinding\n\n'+'\n'.join('#print axioms '+r for r in roots)+'\n')
        expected = helpers.expected_roots(audit)
        report['expected_roots'] = sorted(expected)
        report['reader_controls'] = helpers.parser_controls()
        pin = (ROOT / 'lean/lean-toolchain').read_text().strip()
        if pin != 'leanprover/lean4:v4.35.0':
            raise ValueError('Unexpected Lean toolchain')
        lake = Path.home() / '.elan/toolchains' / pin.replace('/', '--').replace(':', '---') / 'bin/lake'
        report['toolchain'] = pin
        env = os.environ.copy()
        env['LEAN_PATH'] = str(attempt)

        def compile_one(source, negative=False):
            name = source.stem
            print(('Rejecting ' if negative else 'Checking ') + name, flush=True)
            out = attempt / (name + '.olean')
            command = [str(lake), 'env', 'lean', '-j', '1', '-R', str(source.parent), '-o', str(out), str(source)]
            tick = time.monotonic()
            proc = subprocess.run(command, cwd=ROOT / 'lean', env=env, capture_output=True, text=True, timeout=args.timeout)
            log = proc.stdout + proc.stderr
            for suffix, body in [('log', log), ('stdout.log', proc.stdout), ('stderr.log', proc.stderr)]:
                (attempt / (name + '.' + suffix)).write_text(body)
            record = dict(returncode=proc.returncode, seconds=time.monotonic()-tick, command=command,
                          source_sha256=helpers.sha(source), log_sha256=helpers.sha(attempt/(name+'.log')))
            if out.exists():
                record['olean_sha256'] = helpers.sha(out)
            report['negative_controls' if negative else 'lean_build'][name] = record
            save()
            if negative:
                if proc.returncode == 0 or 'error:' not in log or re.search(
                        r'unknown identifier|unknown module|failed to import|unexpected token', log, re.I):
                    raise RuntimeError('Invalid rejection control: ' + name)
                if not re.search(r'unsolved goals|decide.*(?:failed|evaluated)|evaluated to', log, re.I):
                    raise RuntimeError('Missing mathematical rejection diagnostic: ' + name)
                record['status'] = 'REJECTED'
            elif proc.returncode != 0 or helpers.DIAGNOSTIC.search(log) or not out.exists():
                raise RuntimeError(name + ' failed; see ' + rel(attempt/(name+'.log')))

        for path in deps + own:
            compile_one(attempt / 'sources' / path.relative_to(ROOT))
        compile_one(binding)
        compile_one(audit)
        report['axiom_audit'] = helpers.parse_audit((attempt/'Audit.log').read_text(), expected)
        report['audited_roots'] = len(expected)
        wrong = F(found['models']['Baseline']['witnesses']['Below']['output_exact'])
        wrong += F(1, wrong.denominator)
        bad_output = generated / 'BadOutput.lean'
        bad_output.write_text('import Witnesses\nnamespace '+ns+'\nset_option maxRecDepth 100000\n'+
            'example : evalQ Baseline.original belowQ = ['+leanq(wrong)+'] := by decide +kernel\nend '+ns+'\n')
        bad_region = generated / 'BadRegion.lean'
        bad_region.write_text('import Witnesses\nnamespace '+ns+'\nopen PropertyTransfer\n'+
            'example : (farAbove 2).pre belowInput := by\n'+
            '  norm_num [farAbove, physicalX, physicalY, belowInput, belowQ]\nend '+ns+'\n')
        compile_one(bad_output, negative=True)
        compile_one(bad_region, negative=True)
        report['generated_sha256'] = {rel(p): helpers.sha(p) for p in generated.iterdir() if p.is_file()}
        if args.runtime_python:
            # Preserve a virtual environment's interpreter symlink.
            command = [str(args.runtime_python.absolute()), '-B', str(HERE/'runtime.py'),
                       '--search', str(attempt/'SEARCH.json'), '--output', str(attempt/'RUNTIME.json'),
                       '--upstream', str(args.upstream.resolve())]
            proc = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, timeout=args.timeout)
            (attempt/'runtime.log').write_text(proc.stdout+proc.stderr)
            if proc.returncode:
                raise RuntimeError('Runtime replay failed; see ' + rel(attempt/'runtime.log'))
            report['runtime'] = json.loads((attempt/'RUNTIME.json').read_text())
            report['runtime_command'] = command
            report['runtime_sha256'] = helpers.sha(attempt/'RUNTIME.json')
        else:
            report['runtime'] = {'status': 'NOT_RUN'}
        if initial != {rel(p): helpers.sha(p) for p in inputs}:
            raise ValueError('Input changed during verification')
        report['inputs_unchanged'] = True
        report['status'] = 'PASS'
    except Exception as exc:
        report['status'] = 'FAIL'
        report['error'] = str(exc)
    finally:
        report['seconds'] = time.monotonic()-started
        report['finished_utc'] = datetime.now(timezone.utc).isoformat()
        save()
    print(report['status'] + ': ' + rel(RESULT), flush=True)
    if report['status'] != 'PASS':
        print(report.get('error'), file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
