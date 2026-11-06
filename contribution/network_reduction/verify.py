"""Regenerate reduced ONNX models, check Lean proofs, and measure execution.

Run with a Python environment containing numpy, torch, onnx, onnxruntime.
The repository's pinned Lean/mathlib environment must already be installed.
"""
import argparse
from collections import Counter
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import subprocess
import time

from study import HERE, ROOT, BUILD, MODELS, ROOTS, generate, runtime, sha

ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
GENERIC = ['select_map', 'dot_select', 'layer_trim', 'prune_exact', 'zeros_of_bounds',
           'certified_prune', 'networkSetoid', 'certified_equivalent', 'predicate_transfer']
SHARED = ['dot_bounds', 'layer_sound', 'relu_sound', 'exact_layer_trace']
AXIOMS = re.compile(r"'([^'\n]+)' (?:depends on axioms: \[([^\]\n]*)\]|does not depend on any axioms)")


def source_hashes():
    paths = list(HERE.glob('*.lean')) + list(HERE.glob('*.py'))
    paths += [ROOT/'Property2.lean', ROOT/'Float32.lean', ROOT/'universal/IntervalNetwork.lean',
              ROOT/'anchor_view/trained/onnx_model.py']
    paths += [ROOT.parent/'lean'/p for p in ['lean-toolchain', 'lakefile.lean', 'lake-manifest.json']]
    return {str(p.relative_to(ROOT.parent)):sha(p) for p in sorted(paths)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--upstream', required=True, type=Path,
                        help='Local SAIV_2025_Alsomitra checkout at the pinned commit')
    args = parser.parse_args()
    upstream = args.upstream.resolve()
    BUILD.mkdir(parents=True, exist_ok=True)
    result_path = ROOT/'results/network_reduction_verification.json'
    result_path.parent.mkdir(exist_ok=True)
    report = dict(status='RUNNING', timestamp_utc=datetime.now(timezone.utc).isoformat(),
                  scope='Exact real network equality on the raw SAIV unit cube; separate float32 replay')
    def save():
        result_path.write_text(json.dumps(report, indent=2)+'\n')
    save()
    start = time.monotonic()
    try:
        report['generation'] = generate(upstream)
        expected = {'Contribution.Reduction.'+n for n in GENERIC}
        expected |= {'Contribution.Universal.'+n for n in SHARED}
        expected |= {'Contribution.Reduction.'+m+'.'+n for m in MODELS for n in ROOTS}
        audit = HERE/'Audit.lean'
        audit.write_text('import Baseline\nimport Adversarial\n\n' + '\n'.join(
            '#print axioms '+name for name in sorted(expected))+'\n')
        report['sources_sha256'] = source_hashes()
        env = os.environ.copy()
        # Search only this run's local module directory and Lake's pinned dependencies.
        env['LEAN_PATH'] = str(BUILD)
        stages = [('Property2',ROOT/'Property2.lean'), ('Float32',ROOT/'Float32.lean'),
                  ('IntervalNetwork',ROOT/'universal/IntervalNetwork.lean'),
                  ('Pruning',HERE/'Pruning.lean'), ('Baseline',HERE/'Baseline.lean'),
                  ('Adversarial',HERE/'Adversarial.lean'), ('Audit',audit)]
        for name,_ in stages:
            (BUILD/(name+'.olean')).unlink(missing_ok=True)
        report['lean_build'] = {}
        for name, source in stages:
            print('Checking '+name, flush=True)
            tick = time.monotonic()
            args = ['lake','env','lean','-j','1','-R',str(source.parent),
                    '-o',str(BUILD/(name+'.olean')),str(source)]
            proc = subprocess.run(args, cwd=ROOT.parent/'lean', env=env, text=True,
                                  capture_output=True, timeout=1200)
            output = proc.stdout + proc.stderr
            log = BUILD/(name+'.log'); log.write_text(output)
            if proc.returncode or re.search(r'\b(?:error|warning):',output):
                raise RuntimeError(name+' failed:\n'+output)
            report['lean_build'][name] = dict(seconds=time.monotonic()-tick,
                olean_sha256=sha(BUILD/(name+'.olean')), log_sha256=sha(log))
        rows = AXIOMS.findall((BUILD/'Audit.log').read_text())
        counts = Counter(name for name,_ in rows)
        if set(counts) != expected or any(n!=1 for n in counts.values()):
            raise ValueError('Missing, extra, or duplicate proof audit roots')
        report['axiom_audit'] = {}
        for name, raw in rows:
            axioms = {a.strip() for a in raw.split(',') if a.strip()}
            if not axioms <= ALLOWED:
                raise ValueError('Unapproved axiom: '+name+': '+str(axioms))
            report['axiom_audit'][name] = sorted(axioms)
        report['audited_roots'] = len(expected)
        print('Lean passed; checking float32 execution and timing',flush=True)
        report['runtime'] = runtime(upstream)
        if source_hashes() != report['sources_sha256']:
            raise RuntimeError('Source changed during verification')
        for name, data in report['generation']['models'].items():
            if sha(BUILD/(name+'.onnx')) != data['reduced_sha256']:
                raise RuntimeError('Export changed during verification')
        report['status'] = 'PASS'
    except Exception as exc:
        report['status'] = 'FAIL'
        report['error'] = str(exc)
        raise
    finally:
        report['seconds'] = time.monotonic()-start
        save()
    print(json.dumps({'status':report['status'], 'audited_roots':report['audited_roots'],
                      'result':str(result_path.relative_to(ROOT.parent))}, indent=2))


if __name__ == '__main__':
    main()
