"""Build, audit, and demonstrate the ACAS Xu input-region reference checker.

Only Python's standard library and the pinned Lean/Mathlib installation are
required. Builds are isolated from the other experiments. No PyTorch, network
weights, or prior float32 verification receipt is needed for this example.
"""
import argparse
from collections import Counter
from datetime import datetime, timezone
from fractions import Fraction as Q
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

HERE = Path(__file__).resolve().parent
COMPILER = HERE.parent
ROOT = COMPILER.parent
LEAN = ROOT.parent / 'lean'
BUILD = ROOT / '.build/acas'
RESULTS = ROOT / 'results'
CORE = ('RegionSyntax', 'RegionNormalization', 'RegionCheck')
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
AXIOMS = re.compile(r"'([^'\n]+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)")
ROOTS = (
    'forall_coord', 'box_cell_correct', 'conjunction_correct', 'source_correct',
    'printed_region_correct', 'corrected_region_correct', 'reference_check_correct',
    'printed_check_correct', 'corrected_check_correct', 'corrected_agrees_everywhere',
    'loses_valid_input', 'admits_invalid_input', 'boundary_agrees',
    'outer_domain_retained', 'printed_not_equivalent',
)
EXPECTED = {'Contribution.RegionCompiler.Acas.' + name for name in ROOTS}
EXPECTED |= {'Contribution.RegionCompiler.' + name for name in
             ('compile_correct', 'normalized_formula', 'checkNormalized_correct')}
DISTANCE = Q('55947.691')
LOW = tuple(map(Q, (0, -1, -1, 0, 0)))
HIGH = tuple(map(Q, (60000, 1, 1, 1200, 1200)))


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sources():
    paths = [COMPILER / (name + '.lean') for name in CORE]
    paths += [*HERE.glob('*.lean'), HERE / 'verify.py']
    return {str(p.relative_to(ROOT)): sha(p) for p in sorted(paths)}


def call(label, args, expected_code=0):
    env = os.environ.copy()
    env['LEAN_PATH'] = str(BUILD)
    result = subprocess.run(['lake', 'env', 'lean', '-j', '1', *map(str, args)],
                            cwd=LEAN, env=env, text=True, capture_output=True, timeout=180)
    log = result.stdout + result.stderr
    (BUILD / (label + '.log')).write_text(log)
    if result.returncode != expected_code:
        raise RuntimeError(label + ':\n' + log)
    if expected_code == 0 and re.search(r'\b(?:warning|error):', log):
        raise RuntimeError(label + ': unexpected diagnostics:\n' + log)
    return result.stdout


def audit(log):
    rows = AXIOMS.findall(log)
    counts = Counter(name for name, _ in rows)
    if set(counts) != EXPECTED or any(n != 1 for n in counts.values()):
        raise ValueError('Missing, duplicate, or unexpected theorem audit result')
    result = {}
    for name, raw in rows:
        axioms = {s.strip() for s in raw.split(',') if s.strip()}
        if not axioms <= ALLOWED:
            raise ValueError('Untrusted axiom: ' + name)
        result[name] = sorted(axioms)
    return result


def expected_probes():
    def flight(v):
        return tuple(map(Q, (60000, 0, 0, 1200, v)))
    return {
        'valid_50': flight(50),
        'invalid_100': flight(100),
        'boundary_60': flight(60),
        'zero_speed': flight(0),
        'just_below_60': flight(Q('59.999')),
        'just_above_60': flight(Q('60.001')),
        'maximum_speed': flight(1200),
        'negative_speed': flight(-1),
        'above_domain': flight(1201),
        'exact_thresholds': (DISTANCE, Q(0), Q(0), Q(1145), Q(60)),
        'distance_too_low': (DISTANCE-Q('0.001'), Q(0), Q(0), Q(1200), Q(50)),
        'own_speed_too_low': (Q(60000), Q(0), Q(0), Q(1144), Q(50)),
        'angle_outside': (Q(60000), Q(2), Q(0), Q(1200), Q(50)),
        'distance_outside': (Q(60001), Q(0), Q(0), Q(1200), Q(50)),
    }


def check_row(row, expected):
    physical = tuple(map(Q, row['physical']))
    if physical != expected or len(physical) != 5:
        raise ValueError('Unexpected physical point: ' + row['case'])
    normalized = tuple((x-lo)/(hi-lo) for x, lo, hi in zip(physical, LOW, HIGH))
    if tuple(map(Q, row['normalized'])) != normalized:
        raise ValueError('Incorrect coordinate normalization: ' + row['case'])
    rho, _, _, own, intruder = physical
    in_domain = all(lo <= x <= hi for lo, x, hi in zip(LOW, physical, HIGH))
    # Independent direct predicates; this does not reimplement the Lean compiler.
    shared = in_domain and rho >= DISTANCE and own >= 1145
    source = shared and intruder <= 60
    printed = shared and intruder >= 60
    for field, expected_value in (('reference', source), ('printed', printed), ('corrected', source)):
        if type(row[field]) is not bool or row[field] != expected_value:
            raise ValueError('Semantic mismatch: ' + row['case'] + '/' + field)


def show(rows):
    print('\nACAS Xu input-region comparison (exact rational arithmetic)')
    print('Equation (7): intruder <= 60; printed Equation (8): intruder >= 60.')
    print('D and normalization are explicit demonstration choices. No network is evaluated.\n')
    print(f"{'Case':<23} {'Intruder ft/s':>14} {'Eq.7':>7} {'Eq.8':>7} {'Fixed':>7}")
    print('-' * 63)
    for row in rows:
        speed = str(Q(row['physical'][4]))
        values = [('true' if row[k] else 'false') for k in ('reference', 'printed', 'corrected')]
        print(f"{row['case']:<23} {speed:>14} {values[0]:>7} {values[1]:>7} {values[2]:>7}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--point', nargs=5, type=Q,
                        metavar=('RHO', 'THETA', 'PSI', 'OWN', 'INTRUDER'),
                        help='Also check a physical point; decimal strings and n/d fractions are exact')
    args = parser.parse_args()
    BUILD.mkdir(parents=True, exist_ok=True)
    RESULTS.mkdir(exist_ok=True)
    start = time.monotonic()
    report = dict(status='RUNNING', timestamp_utc=datetime.now(timezone.utc).isoformat(),
                  scope='Input-region translation of Equations (7) and (8), with an explicit demonstration domain',
                  source='https://arxiv.org/pdf/2505.00466v2#page=8',
                  network_property_proved=False, upstream_execution_reproduced=False,
                  domain=dict(lower=list(map(str, LOW)), upper=list(map(str, HIGH))))
    path = RESULTS / 'acas_checker_verification.json'
    path.write_text(json.dumps(report, indent=2)+'\n')
    try:
        initial = sources()
        report['lean_version'] = call('version', ['--version']).strip()
        if 'version 4.35.0,' not in report['lean_version']:
            raise ValueError('Expected Lean 4.35.0 from lean/lean-toolchain')
        report['mathlib_manifest_sha256'] = sha(LEAN/'lake-manifest.json')
        modules = [(name, COMPILER) for name in CORE] + [('AcasExample', HERE)]
        for name, folder in modules:
            artifact = BUILD / (name+'.olean')
            artifact.unlink(missing_ok=True)
            call(name, ['-R', folder, '-o', artifact, folder/(name+'.lean')])
            print('Kernel-checked ' + name, flush=True)
        log = call('audit', ['-R', HERE, HERE/'Audit.lean'])
        report['theorems'] = audit(log)
        matches = list(AXIOMS.finditer(log))
        bad_logs = ('', log[:matches[-1].start()], log+matches[0].group(0), log.replace('propext','sorryAx',1))
        for bad in bad_logs:
            try:
                audit(bad)
            except ValueError:
                pass
            else:
                raise RuntimeError('Invalid proof audit was accepted')
        report['audit_negative_controls'] = len(bad_logs)
        rows = [json.loads(line) for line in call('runtime', ['--run', HERE/'AcasMain.lean']).splitlines()]
        expected = expected_probes()
        if [row['case'] for row in rows] != list(expected):
            raise ValueError('Missing, duplicate, or reordered runtime cases')
        for row in rows:
            check_row(row, expected[row['case']])
        report['runtime'] = dict(cases=len(rows), decisions=len(rows)*3, examples=rows,
                                 oracle='Independent direct Python Fraction predicates')
        for label, values in (('zero_denominator', ['0','0','0','0','1/0']),
                              ('wrong_arity', ['1','2']), ('invalid_number', ['bad','0','0','0','0'])):
            call(label, ['--run', HERE/'AcasMain.lean', *values], expected_code=2)
        report['input_negative_controls'] = 3
        show(rows)
        if args.point is not None:
            custom = json.loads(call('custom', ['--run', HERE/'AcasMain.lean', *map(str,args.point)]))
            check_row(custom, tuple(args.point))
            report['custom'] = custom
            show([custom])
            print('Physical:', ', '.join(custom['physical']))
            print('Normalized:', ', '.join(custom['normalized']))
        if sources() != initial:
            raise RuntimeError('Sources changed during verification')
        report['sources_sha256'] = initial
        report['artifacts_sha256'] = {str((BUILD/(name+'.olean')).relative_to(ROOT)):
                                     sha(BUILD/(name+'.olean')) for name, _ in modules}
        report['status'] = 'PASS'
        print(f"\nPASS: {len(report['theorems'])} audited roots; {len(rows)} cases; {len(rows)*3} checked decisions.")
        print('Corrected translation agrees with the source for every rational input and positive affine normalizer.')
    except Exception as error:
        report.update(status='FAIL', error=str(error))
        raise
    finally:
        report['elapsed_seconds'] = round(time.monotonic()-start, 3)
        path.write_text(json.dumps(report, indent=2, sort_keys=True)+'\n')


if __name__ == '__main__':
    main()
