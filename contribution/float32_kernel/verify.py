"""Kernel-check the rounding proof and its connection to frozen Property2.

A PASS certifies the stated arithmetic model, not Apple Accelerate refinement.
"""
from collections import Counter
from datetime import datetime,timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time

from generate import generate

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
BUILD = ROOT/'.build'
RESULTS = ROOT/'results'
LEAN = ROOT.parent/'lean'
MODULES = ('Rounding','RoundingExistence','RoundedNetwork','ReductionExistence',
           'KernelBounds','FrozenRounding','KernelNegativeControls')
ALLOWED = {'propext','Classical.choice','Quot.sound'}
AXIOMS = re.compile(r"'([^'\n]+)' (?:depends on axioms: \[([^\]\n]*)\]|does not depend on any axioms)")
GROUPS = {
    'Contribution.Binary32': (
        'delta_positive','nearby','nearest_error','mass_nonnegative','exact_le_mass',
        'expression_error','expression_within_neuron_budget','finite_values','finite_zero',
        'nearest_exists','nearestChoice_correct','terms_exact','terms_mass','terms_cost',
        'products_sum','magnitude_bound','products_mass_bound','neuron_mass_bound',
        'reduction_approx','rounded_layer_trace','sequential_terms','sequential_reduction',
        'runLayer_trace','network_execution_exists'),
    'Contribution.KernelBounds': ('first_safe','second_safe','third_safe','first_range',
        'second_range','first_mass','second_mass','third_mass'),
    'Contribution.Frozen': ('rounded_execution_trace','rounded_all_inputs','property2_rounded',
        'rounded_observed_satisfied','rounded_output_length','rounded_property_nonvacuous'),
    'Contribution.Binary32.Controls': ('reject_bad_rounding','reject_insufficient_budget',
        'reject_duplicated_terms','reject_invalid_neuron'),
}
EXPECTED = {ns+'.'+name for ns,names in GROUPS.items() for name in names}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def hashes():
    paths = list(HERE.glob('*.lean'))+list(HERE.glob('*.py'))+list(HERE.glob('*.c'))
    return {str(p.relative_to(ROOT)):sha(p) for p in sorted(paths)}


def call(name,args):
    env = os.environ.copy()
    env['LEAN_PATH'] = str(BUILD)+(os.pathsep+env['LEAN_PATH'] if env.get('LEAN_PATH') else '')
    result = subprocess.run(['lake','env','lean','-j','1',*map(str,args)],cwd=LEAN,
        env=env,text=True,capture_output=True,timeout=900)
    log = result.stdout+result.stderr
    (RESULTS/('rounding_'+name+'.log')).write_text(log)
    if result.returncode or re.search(r'\b(?:warning|error):',log):
        raise RuntimeError(name+':\n'+log)
    return log


def audit(log):
    rows = AXIOMS.findall(log)
    counts = Counter(name for name,_ in rows)
    if set(counts) != EXPECTED or any(n != 1 for n in counts.values()):
        raise ValueError('incomplete or duplicated theorem audit')
    result = {}
    for name,raw in rows:
        axioms = {a.strip() for a in raw.split(',') if a.strip()}
        if not axioms <= ALLOWED:
            raise ValueError('untrusted axiom in '+name+': '+repr(axioms))
        result[name] = sorted(axioms)
    return result


def checked_dependencies():
    deps = {}
    for name in ('float32_verification','universal_verification'):
        path = RESULTS/(name+'.json')
        report = json.loads(path.read_text())
        if report['status'] != 'PASS':
            raise ValueError('prerequisite not checked: '+name)
        for field in ('sources_sha256','artifacts_sha256'):
            for relative,expected in report[field].items():
                if sha(ROOT/relative) != expected:
                    raise ValueError('stale prerequisite: '+relative)
                deps[relative] = expected
        deps[str(path.relative_to(ROOT))] = sha(path)
    return deps


def main():
    start = time.monotonic()
    report = dict(status='RUNNING',timestamp_utc=datetime.now(timezone.utc).isoformat(),
        scope='Universal frozen Property2 under finite-binary32 nearest-rounding reduction semantics',
        pytorch_universal_status='NOT_PROVED',trained=False,
        remaining_obligation='Show actual PyTorch/Apple Accelerate execution refines RoundedNetwork with CorrectRounding')
    path = RESULTS/'rounding_verification.json'
    path.write_text(json.dumps(report,indent=2)+'\n')
    try:
        report['dependencies_sha256'] = checked_dependencies()
        report['numerical_bounds'] = generate()
        audit_path = HERE/'RoundingAudit.lean'
        audit_path.write_text('import KernelNegativeControls\n\n'+
            '\n'.join('#print axioms '+n for n in sorted(EXPECTED))+'\n')
        initial = hashes()
        version = call('version',['--version']).strip()
        if 'version 4.35.0,' not in version:
            raise ValueError('unexpected Lean version')
        report['lean_version'] = version
        report['mathlib_manifest_sha256'] = sha(LEAN/'lake-manifest.json')
        if json.loads((RESULTS/'universal_verification.json').read_text())['lean_version'] != version:
            raise ValueError('toolchain differs from universal proof')
        # Validate the original proof's Mathlib environment as well as its files.
        cache = json.loads((BUILD/'universal_build_cache.json').read_text())
        for entry in cache.values():
            if entry['key']['mathlib_manifest'] != report['mathlib_manifest_sha256']:
                raise ValueError('Mathlib differs from checked universal build')
        for module in MODULES:
            artifact = BUILD/(module+'.olean')
            artifact.unlink(missing_ok=True)
            call(module,['-R',HERE,'-o',artifact,HERE/(module+'.lean')])
            print('Kernel-checked '+module,flush=True)
        log = call('audit',['-R',HERE,audit_path])
        report['theorems'] = audit(log)
        lines = log.splitlines(keepends=True)
        controls = ('',''.join(lines[:-1]),log+lines[0],log.replace('propext','sorryAx',1))
        for bad in controls:
            try:
                audit(bad)
            except ValueError:
                pass
            else:
                raise RuntimeError('bad audit accepted')
        report['audit_negative_controls'] = len(controls)
        report['invalid_claims_rejected'] = sorted(GROUPS['Contribution.Binary32.Controls'])
        if hashes() != initial or checked_dependencies() != report['dependencies_sha256']:
            raise RuntimeError('inputs changed during check')
        report['sources_sha256'] = initial
        report['artifacts_sha256'] = {str((BUILD/(n+'.olean')).relative_to(ROOT)):
            sha(BUILD/(n+'.olean')) for n in MODULES}
        report['status'] = 'PASS'
        print('Rounding proof PASS:',len(report['theorems']),'audited theorem roots',flush=True)
        print('Actual PyTorch/Apple Accelerate universal refinement: NOT_PROVED',flush=True)
    except Exception as error:
        report.update(status='FAIL',error=str(error))
        raise
    finally:
        report['elapsed_seconds'] = round(time.monotonic()-start,3)
        path.write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')


if __name__ == '__main__':
    main()
