"""Rebuild and audit the output-update contract without regenerating old evidence.

Every invocation gets a fresh local build directory and a retained receipt.
Only the pinned Lake dependencies are reused. No ONNX exporter, training loop,
float32 comparison, or benchmark is run by this verifier.
"""

import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import itertools
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time

sys.dont_write_bytecode = True

HERE = Path(__file__).resolve().parent
CONTRIBUTION = HERE.parent.parent
ROOT = CONTRIBUTION.parent
BUILD_ROOT = CONTRIBUTION / '.build' / 'output_updates'
OLD_RECEIPT = CONTRIBUTION / 'results' / 'network_reduction_verification.json'
OLD_PDF = HERE.parent / 'NETWORK_REDUCTION.pdf'
RESULT = CONTRIBUTION / 'results' / 'output_update_verification.json'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
AUDIT_COMMAND = re.compile(r'^\s*#print\s+axioms\s+([A-Za-z_][A-Za-z_0-9.\']*)\s*$')
AXIOMS = re.compile(
    r"'([^'\r\n]+)' (?:depends on axioms: \["
    r"(\s*(?:[A-Za-z_][A-Za-z_0-9.']*"
    r"(?:\s*,\s*[A-Za-z_][A-Za-z_0-9.']*)*)?\s*)"
    r"\]|does not depend on any axioms)"
)
DIAGNOSTIC = re.compile(r'\b(?:error|warning):')
SCOPE = ('Rational output-head updates with a domain-typed input; '
         'fresh Lean proofs and axiom audit, not new float32 or ONNX evidence')


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def relative(path):
    return str(Path(path).relative_to(ROOT))


def save_json(path, value):
    """Atomically update this run's receipt or the separate latest-run index."""
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.is_symlink():
        raise ValueError('Refusing a symbolic-link receipt: ' + str(path))
    with tempfile.NamedTemporaryFile(
            mode='w', encoding='ascii', dir=str(path.parent),
            prefix='.' + path.name + '.', suffix='.tmp', delete=False) as stream:
        temporary = Path(stream.name)
        json.dump(value, stream, indent=2, ensure_ascii=True)
        stream.write('\n')
    os.replace(str(temporary), str(path))


def new_attempt():
    BUILD_ROOT.mkdir(parents=True, exist_ok=True)
    for number in itertools.count(1):
        path = BUILD_ROOT / ('attempt-%03d' % number)
        try:
            path.mkdir()
            return path
        except FileExistsError:
            continue


def expected_roots(audit):
    names = []
    for line in audit.read_text(encoding='utf-8').splitlines():
        match = AUDIT_COMMAND.fullmatch(line)
        if match:
            names.append(match.group(1))
        elif line.lstrip().startswith('#print'):
            raise ValueError('Unsupported audit print command: ' + line)
    if not names or len(names) != len(set(names)):
        raise ValueError('Audit roots must be nonempty and distinct')
    return set(names)


def parse_audit(output, expected):
    """Consume full records, including wrapped lists; reject unchecked text."""
    rows = []
    position = 0
    while position < len(output):
        while position < len(output) and output[position].isspace():
            position += 1
        if position == len(output):
            break
        match = AXIOMS.match(output, position)
        if not match:
            raise ValueError('Malformed or unexpected audit output at character ' +
                             str(position) + ': ' + repr(output[position:position + 160]))
        rows.append(match.groups())
        position = match.end()
        if position < len(output) and not output[position].isspace():
            raise ValueError('Audit records must be separated by whitespace')
    counts = Counter(name for name, _ in rows)
    if set(counts) != expected or any(number != 1 for number in counts.values()):
        raise ValueError('Missing, extra, or duplicate proof audit roots')
    result = {}
    for name, raw in rows:
        axioms = {item.strip() for item in (raw or '').split(',') if item.strip()}
        if not axioms <= ALLOWED:
            raise ValueError('Unapproved axiom for ' + name + ': ' + str(sorted(axioms)))
        result[name] = sorted(axioms)
    return result


def parser_controls():
    """Exercise this reader's fail-closed behavior, without invoking Lean."""
    first = "'Control.first' does not depend on any axioms"
    second = "'Control.second' depends on axioms: [propext, Classical.choice, Quot.sound]"
    expected = {'Control.first', 'Control.second'}
    good = first + '\n' + second + '\n'
    parsed = parse_audit(good, expected)
    if parsed != {'Control.first': [], 'Control.second': sorted(ALLOWED)}:
        raise RuntimeError('Positive axiom-reader control failed')
    wrapped = (first + "\n'Control.second' depends on axioms: [propext,\n"
               ' Classical.choice,\n Quot.sound]\n')
    if parse_audit(wrapped, expected) != parsed:
        raise RuntimeError('Positive multiline axiom-reader control failed')
    samples = {
        'missing_root': first,
        'duplicate_root': good + first,
        'unexpected_root': good + "'Control.extra' does not depend on any axioms",
        'foreign_axiom': first + "\n'Control.second' depends on axioms: [Control.foreign]",
        'sorry_axiom': first + "\n'Control.second' depends on axioms: [sorryAx]",
        'native_trust_axiom': first + "\n'Control.second' depends on axioms: [Lean.ofReduceBool]",
        'malformed_axiom_list': first + "\n'Control.second' depends on axioms: [propext",
        'truncated_multiline_list': (first + "\n'Control.second' depends on axioms: [propext,\n"
                                     ' Classical.choice'),
        'missing_continuation_comma': (first + "\n'Control.second' depends on axioms: [propext\n"
                                       ' Classical.choice]'),
        'empty_continuation_item': (first + "\n'Control.second' depends on axioms: [propext,\n"
                                    ', Quot.sound]'),
        'embedded_root_in_unclosed_list': (first + "\n'Control.second' depends on axioms: [propext,\n"
                                           "'Control.extra' does not depend on any axioms"),
        'foreign_multiline_axiom': (first + "\n'Control.second' depends on axioms: [propext,\n"
                                    ' Control.foreign]'),
        'trailing_unchecked_text': good + 'unchecked audit output',
        'wrapped_trailing_garbage': wrapped + 'unchecked audit output',
        'stray_continuation_after_list': wrapped + ' Quot.sound]',
        'leading_unchecked_text': 'unchecked audit output\n' + wrapped,
        'warning_diagnostic': good + 'warning: declaration uses sorry',
        'error_diagnostic': good + 'error: unknown identifier',
    }
    result = {'scope': 'Synthetic reader controls, not compiler mutation experiments',
              'positive_complete_audit': 'ACCEPTED',
              'positive_multiline_audit': 'ACCEPTED'}
    for name, sample in samples.items():
        try:
            parse_audit(sample, expected)
        except ValueError:
            result[name] = 'REJECTED'
        else:
            raise RuntimeError('Axiom-reader control was wrongly accepted: ' + name)
    for name in ['warning', 'error']:
        if DIAGNOSTIC.search('file.lean:1:0: ' + name + ': control') is None:
            raise RuntimeError('Compiler diagnostic control missed ' + name)
        result['compiler_' + name + '_detected'] = True
    return result


def check_old_receipt():
    """Require current old sources to match the untouched completed study."""
    receipt = json.loads(OLD_RECEIPT.read_text(encoding='utf-8'))
    if receipt.get('status') != 'PASS':
        raise ValueError('Original network-reduction receipt is not PASS')
    bindings = receipt.get('sources_sha256')
    if not isinstance(bindings, dict) or not bindings:
        raise ValueError('Original receipt has no source bindings')
    paths = []
    for name, digest in bindings.items():
        path = ROOT / name
        # Refuse a receipt that tries to expand this local audit outside ROOT.
        path.resolve().relative_to(ROOT.resolve())
        if sha(path) != digest:
            raise ValueError('Original reduction source binding changed: ' + name)
        paths.append(path)
    return paths


def hashes(paths):
    return {relative(path): sha(path) for path in sorted(set(paths))}


def snapshot_sources(attempt, paths):
    for source in sorted(set(paths)):
        target = attempt / 'sources' / source.relative_to(ROOT)
        target.parent.mkdir(parents=True, exist_ok=True)
        with target.open('xb') as stream:
            stream.write(source.read_bytes())


def decoded(value):
    if isinstance(value, bytes):
        return value.decode('utf-8', errors='replace')
    return value or ''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--timeout', type=int, default=1200,
                        help='Wall-time limit in seconds for each Lean stage')
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error('--timeout must be positive')

    attempt = new_attempt()
    attempt_receipt = attempt / 'RESULT.json'
    report = dict(status='RUNNING', timestamp_utc=datetime.now(timezone.utc).isoformat(),
                  scope=SCOPE, attempt=relative(attempt), lean_build={})
    started = time.monotonic()
    initial = None
    inputs = []

    def save():
        save_json(attempt_receipt, report)
        save_json(RESULT, report)

    save()
    error = None
    try:
        report['reader_controls'] = parser_controls()
        old_sources = check_old_receipt()
        stages = [
            ('Property2', CONTRIBUTION / 'Property2.lean'),
            ('Float32', CONTRIBUTION / 'Float32.lean'),
            ('IntervalNetwork', CONTRIBUTION / 'universal' / 'IntervalNetwork.lean'),
            ('Pruning', HERE.parent / 'Pruning.lean'),
            ('Adversarial', HERE.parent / 'Adversarial.lean'),
            ('OutputUpdates', HERE / 'OutputUpdates.lean'),
            ('Audit', HERE / 'Audit.lean'),
        ]
        inputs = old_sources + [OLD_RECEIPT, OLD_PDF, Path(__file__).resolve()]
        inputs += [source for _, source in stages]
        initial = hashes(inputs)
        report['sources_sha256'] = initial
        report['original_receipt_sha256'] = sha(OLD_RECEIPT)
        report['original_pdf_sha256'] = sha(OLD_PDF)
        report['original_bound_sources'] = len(old_sources)
        snapshot_sources(attempt, inputs)
        expected = expected_roots(HERE / 'Audit.lean')
        report['expected_roots'] = sorted(expected)

        pin = (ROOT / 'lean' / 'lean-toolchain').read_text(encoding='ascii').strip()
        if pin != 'leanprover/lean4:v4.35.0':
            raise ValueError('Unexpected Lean toolchain: ' + pin)
        lake = (Path.home() / '.elan' / 'toolchains' /
                pin.replace('/', '--').replace(':', '---') / 'bin' / 'lake')
        if not lake.is_file():
            raise ValueError('Pinned Lake executable is missing: ' + str(lake))
        report['toolchain'] = pin
        report['lake'] = str(lake)

        env = os.environ.copy()
        # Lake adds pinned package dependencies; no old local proof artifacts
        # are present in this fresh path or inherited through LEAN_PATH.
        env['LEAN_PATH'] = str(attempt)
        for name, source in stages:
            print('Checking ' + name, flush=True)
            copied = attempt / 'sources' / source.relative_to(ROOT)
            output_path = attempt / (name + '.olean')
            command = [str(lake), 'env', 'lean', '-j', '1', '-R', str(copied.parent),
                       '-o', str(output_path), str(copied)]
            tick = time.monotonic()
            timeout = False
            try:
                proc = subprocess.run(command, cwd=ROOT / 'lean', env=env, text=True,
                                      capture_output=True, timeout=args.timeout)
                stdout, stderr = proc.stdout, proc.stderr
                returncode = proc.returncode
            except subprocess.TimeoutExpired as exc:
                timeout = True
                stdout, stderr = decoded(exc.stdout), decoded(exc.stderr)
                returncode = None
            output = stdout + stderr
            for suffix, content in [('stdout.log', stdout), ('stderr.log', stderr),
                                    ('log', output)]:
                with (attempt / (name + '.' + suffix)).open('x', encoding='utf-8') as stream:
                    stream.write(content)
            stage = dict(seconds=time.monotonic() - tick, command=command,
                         returncode=returncode, timed_out=timeout,
                         log_sha256=sha(attempt / (name + '.log')),
                         stdout_sha256=sha(attempt / (name + '.stdout.log')),
                         stderr_sha256=sha(attempt / (name + '.stderr.log')))
            if output_path.exists():
                stage['olean_sha256'] = sha(output_path)
            report['lean_build'][name] = stage
            save()
            if timeout or returncode != 0 or DIAGNOSTIC.search(output):
                raise RuntimeError(name + ' failed; inspect ' + relative(attempt / (name + '.log')))
            if not output_path.is_file():
                raise RuntimeError(name + ' produced no fresh .olean')

        audit = (attempt / 'Audit.log').read_text(encoding='utf-8')
        report['axiom_audit'] = parse_audit(audit, expected)
        report['audited_roots'] = len(expected)
        report['status'] = 'PASS'
    except Exception as exc:
        report['status'] = 'FAIL'
        report['error'] = type(exc).__name__ + ': ' + str(exc)
        error = exc
    finally:
        if initial is not None:
            try:
                after = hashes(inputs)
                report['sources_sha256_after'] = after
                report['inputs_unchanged'] = after == initial
                if after != initial:
                    raise RuntimeError('Source or original evidence changed during verification')
                # Validate the historical source bindings once again rather
                # than merely observing unchanged runner-local input hashes.
                check_old_receipt()
            except Exception as exc:
                report['status'] = 'FAIL'
                report['integrity_error'] = type(exc).__name__ + ': ' + str(exc)
                if error is None:
                    error = exc
        report['seconds'] = time.monotonic() - started
        report['finished_utc'] = datetime.now(timezone.utc).isoformat()
        save()

    print(json.dumps(dict(status=report['status'], audited_roots=report.get('audited_roots', 0),
                          attempt=relative(attempt), result=relative(RESULT)), indent=2))
    if error is not None:
        print(report.get('error', report.get('integrity_error', str(error))), file=sys.stderr)
        return 1
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
