"""Fresh Lean audit of symmetric RMSProp and controller-property transfer."""
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
NETWORK = HERE.parent
CONTRIBUTION = NETWORK.parent
ROOT = CONTRIBUTION.parent
BUILD = CONTRIBUTION / '.build/rmsprop_symmetric'
RESULT = CONTRIBUTION / 'results/rmsprop_and_property_transfer_verification.json'
HELPER = NETWORK / 'output_updates/verify.py'
module_spec = importlib.util.spec_from_file_location('audit_helpers', HELPER)
helpers = importlib.util.module_from_spec(module_spec)
module_spec.loader.exec_module(helpers)


def rel(path):
    return str(Path(path).relative_to(ROOT))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--timeout', type=int, default=1200)
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error('Timeout must be positive')
    BUILD.mkdir(parents=True, exist_ok=True)
    for i in itertools.count(1):
        attempt = BUILD / ('attempt-%03d' % i)
        try:
            attempt.mkdir()
            break
        except FileExistsError:
            continue
    report = dict(status='RUNNING', attempt=rel(attempt),
                  timestamp_utc=datetime.now(timezone.utc).isoformat(),
                  scope='Exact real equal-history RMSProp; separately, property transfer for trained checkpoint reductions and rational momentum',
                  fresh_proof_run=True, second_kernel_run=False,
                  new_float32_or_onnx_run=False, lean_build={}, negative_controls={})
    started = time.monotonic()

    def save():
        helpers.save_json(attempt / 'RESULT.json', report)
        helpers.save_json(RESULT, report)

    save()
    try:
        old = CONTRIBUTION / 'results/linear_observations_verification.json'
        prior = json.loads(old.read_text())
        if prior.get('status') != 'PASS':
            raise ValueError('Prior linear-observation audit must be PASS')
        dependencies = [
            CONTRIBUTION / 'Property2.lean', CONTRIBUTION / 'Float32.lean',
            CONTRIBUTION / 'universal/IntervalNetwork.lean',
            NETWORK / 'Pruning.lean', NETWORK / 'Baseline.lean', NETWORK / 'Adversarial.lean',
            NETWORK / 'output_updates/OutputUpdates.lean',
            NETWORK / 'update_synthesis/AffineRetention.lean',
            NETWORK / 'update_synthesis/NetworkRetention.lean',
            NETWORK / 'linear_observations/MomentumQuotient.lean',
            NETWORK / 'linear_observations/AdaptiveBoundary.lean',
        ]
        # Require every reused proof source to retain its historical binding.
        # Old REPORT/PDF bindings describe old editions, not current proof inputs.
        bindings = prior['sources_sha256']
        for path in dependencies:
            if bindings.get(rel(path)) != helpers.sha(path):
                raise ValueError('Historical proof source changed: ' + rel(path))
        report['historical_proof_bindings'] = {rel(p): helpers.sha(p) for p in dependencies}
        own = [HERE / 'SymmetricRMSProp.lean', NETWORK / 'property_transfer/PropertyTransfer.lean']
        old_receipts = [CONTRIBUTION / 'results' / n for n in [
            'network_reduction_verification.json', 'output_update_verification.json',
            'update_synthesis_verification.json', 'linear_observations_verification.json']]
        config = [ROOT / 'lean' / n for n in ['lean-toolchain', 'lakefile.lean', 'lake-manifest.json']]
        inputs = sorted(set(dependencies + own + old_receipts + config + [HELPER,
            Path(__file__).resolve(), HERE / 'README.md', NETWORK / 'property_transfer/README.md']))
        initial = {rel(p): helpers.sha(p) for p in inputs}
        report['sources_sha256'] = initial
        report['historical_receipts_sha256'] = {rel(p): helpers.sha(p) for p in old_receipts}
        helpers.snapshot_sources(attempt, inputs)
        generated = attempt / 'generated'
        generated.mkdir()
        roots = []
        for path in own:
            source = path.read_text()
            namespace = re.search(r'^namespace (\S+)$', source, re.M).group(1)
            roots.extend(namespace + '.' + n for n in re.findall(r'^theorem (\w+)', source, re.M))
        roots += ['Contribution.Reduction.SymmetricRMSProp.stateSetoid',
                  'Contribution.Reduction.AdaptiveBoundary.no_reduced_step',
                  'Contribution.Reduction.Baseline.all_real_inputs',
                  'Contribution.Reduction.Adversarial.all_real_inputs',
                  'Contribution.Reduction.MomentumQuotient.network_sequence']
        audit = generated / 'Audit.lean'
        audit.write_text('import SymmetricRMSProp\nimport PropertyTransfer\n\n' +
                         '\n'.join('#print axioms ' + r for r in roots) + '\n')
        expected = helpers.expected_roots(audit)
        report['expected_roots'] = sorted(expected)
        report['reader_controls'] = helpers.parser_controls()
        pin = (ROOT / 'lean/lean-toolchain').read_text().strip()
        if pin != 'leanprover/lean4:v4.35.0':
            raise ValueError('Unexpected toolchain: ' + pin)
        lake = Path.home() / '.elan/toolchains' / pin.replace('/', '--').replace(':', '---') / 'bin/lake'
        report['toolchain'] = pin
        env = os.environ.copy()
        env['LEAN_PATH'] = str(attempt)

        def compile_one(source, negative=False):
            name = source.stem
            print(('Rejecting mutation ' if negative else 'Checking ') + name, flush=True)
            output = attempt / (name + '.olean')
            command = [str(lake), 'env', 'lean', '-j', '1', '-R', str(source.parent),
                       '-o', str(output), str(source)]
            tick = time.monotonic()
            proc = subprocess.run(command, cwd=ROOT / 'lean', env=env, text=True,
                                  capture_output=True, timeout=args.timeout)
            log = proc.stdout + proc.stderr
            for suffix, body in [('log', log), ('stdout.log', proc.stdout), ('stderr.log', proc.stderr)]:
                (attempt / (name + '.' + suffix)).write_text(body)
            record = dict(returncode=proc.returncode, seconds=time.monotonic()-tick,
                          command=command, source_sha256=helpers.sha(source),
                          log_sha256=helpers.sha(attempt / (name + '.log')))
            if output.exists():
                record['olean_sha256'] = helpers.sha(output)
            report['negative_controls' if negative else 'lean_build'][name] = record
            save()
            if negative:
                if proc.returncode == 0 or 'unsolved goals' not in log or re.search(
                        r'unknown identifier|unknown module|failed to import|unexpected token', log, re.I):
                    raise RuntimeError('Invalid mutation rejection: ' + name)
                record['status'] = 'REJECTED_UNSOLVED_EQUALITY'
            elif proc.returncode != 0 or helpers.DIAGNOSTIC.search(log) or not output.exists():
                raise RuntimeError(name + ' failed; see ' + rel(attempt / (name + '.log')))

        for source in dependencies + own:
            compile_one(attempt / 'sources' / source.relative_to(ROOT))
        compile_one(audit)
        report['axiom_audit'] = helpers.parse_audit((attempt / 'Audit.log').read_text(), expected)
        report['audited_roots'] = len(expected)
        text = own[0].read_text()
        needle = 'y 1-2*g/(Real.sqrt (v 1/2)+1)'
        if text.count(needle) != 1:
            raise ValueError('Missing/ambiguous aggregate mutation target')
        bad = generated / 'BadAggregate.lean'
        bad.write_text(text.replace(needle, 'y 1-g/(Real.sqrt (v 1/2)+1)'))
        compile_one(bad, negative=True)
        report['generated_sha256'] = {rel(p): helpers.sha(p) for p in generated.iterdir() if p.is_file()}
        final = {rel(p): helpers.sha(p) for p in inputs}
        if initial != final:
            raise ValueError('An input changed during verification')
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
