#!/usr/bin/env python3
"""Download pinned sources, verify every file, and prepare separate work copies.

Uses Python's standard library only. It never executes upstream code or
overwrites an existing experimental work directory.
"""

import argparse
import concurrent.futures
import datetime
import hashlib
import json
import shutil
import tarfile
import tempfile
import urllib.request
from pathlib import Path, PurePosixPath

ROOT = Path(__file__).resolve().parent
REFERENCE_REL = 'python_training/data/Training_Data_Normalised.csv'
REFERENCE_COMMIT = 'e9f6f1c52e0e5349455d2b4f69c2015567d3037f'
REFERENCE_SHA = 'd0b84c0e372a25f7934953ae8adac8db08b7a3b241892a1aa697834f583acbf7'


def prepare_reference(verify_only):
    """Acquire only the pinned CSV needed by the repaired-controller proof."""
    target = ROOT / 'inputs/Training_Data_Normalised.csv'
    if target.exists():
        if sha256(target) != REFERENCE_SHA:
            raise ValueError('Reference CSV hash differs; existing file preserved')
    else:
        if verify_only:
            raise FileNotFoundError('Reference CSV has not been prepared')
        local = ROOT / 'upstream/saiv' / REFERENCE_REL
        if local.exists():
            data = local.read_bytes()
        else:
            url = ('https://raw.githubusercontent.com/ckessler2/SAIV_2025_Alsomitra/'
                   + REFERENCE_COMMIT + '/' + REFERENCE_REL)
            request = urllib.request.Request(url, headers={'User-Agent': 'alsomitra-reference/1.0'})
            with urllib.request.urlopen(request, timeout=60) as response:
                data = response.read()
        if hashlib.sha256(data).hexdigest() != REFERENCE_SHA:
            raise ValueError('Downloaded reference CSV does not match the pinned source')
        target.parent.mkdir(parents=True, exist_ok=True)
        with target.open('xb') as stream:
            stream.write(data)
    print('PASS: pinned 360-row reference CSV is ready.', flush=True)


def sha256(path):
    with path.open('rb') as stream:
        h = hashlib.sha256()
        for block in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(block)
        return h.hexdigest()


def verify_tree(folder, source):
    expected = {item['path']: item for item in source['files']}
    actual = {}
    for path in folder.rglob('*'):
        if path.is_symlink():
            raise ValueError(f'Unexpected symlink: {path}')
        if path.is_file():
            actual[path.relative_to(folder).as_posix()] = path
    if actual.keys() != expected.keys():
        raise ValueError(f"File inventory mismatch for {source['name']}")
    for rel, entry in expected.items():
        path = actual[rel]
        if path.stat().st_size != entry['size'] or sha256(path) != entry['sha256']:
            raise ValueError(f'Content mismatch: {path}')
    return {'files': len(expected), 'bytes': sum(e['size'] for e in expected.values())}


def extract_checked(archive, target, source):
    expected = {item['path']: item for item in source['files']}
    found = set()
    prefix = None
    with tarfile.open(archive, 'r:gz') as tar:
        for member in tar:
            parts = PurePosixPath(member.name).parts
            if not parts or member.name.startswith('/') or '..' in parts:
                raise ValueError(f'Unsafe archive path: {member.name}')
            if prefix is None:
                prefix = parts[0]
            if parts[0] != prefix:
                raise ValueError('Multiple archive roots')
            if member.isdir():
                continue
            rel = PurePosixPath(*parts[1:]).as_posix()
            if not member.isfile() or rel not in expected or rel in found:
                raise ValueError(f'Unexpected archive member: {member.name}')
            if member.size != expected[rel]['size']:
                raise ValueError(f'Unexpected archive size: {rel}')
            destination = target / rel
            destination.parent.mkdir(parents=True, exist_ok=True)
            with tar.extractfile(member) as incoming, destination.open('wb') as outgoing:
                shutil.copyfileobj(incoming, outgoing)
            destination.chmod(0o755 if expected[rel]['executable'] else 0o644)
            found.add(rel)
    verify_tree(target, source)


def obtain(source, verify_only):
    name = source['name']
    target = ROOT / 'upstream' / name
    archive = ROOT / '.downloads' / f"{name}-{source['commit']}.tar.gz"
    if not target.exists():
        if verify_only:
            raise FileNotFoundError(f'Missing snapshot: {target}')
        archive.parent.mkdir(parents=True, exist_ok=True)
        if not archive.exists():
            partial = archive.with_suffix('.part')
            request = urllib.request.Request(source['archive_url'], headers={
                'User-Agent': 'alsomitra-repair-inputs/1.0'})
            try:
                with urllib.request.urlopen(request, timeout=60) as incoming, partial.open('wb') as outgoing:
                    shutil.copyfileobj(incoming, outgoing)
                partial.replace(archive)
            finally:
                partial.unlink(missing_ok=True)
        target.parent.mkdir(parents=True, exist_ok=True)
        with tempfile.TemporaryDirectory(prefix=f'.{name}-', dir=target.parent) as tmp:
            extracted = Path(tmp) / 'snapshot'
            extracted.mkdir()
            extract_checked(archive, extracted, source)
            extracted.rename(target)
    stats = verify_tree(target, source)
    print(f"PASS {name}: {stats['files']} original files", flush=True)
    return {'name': name, 'commit': source['commit'], 'repository': source['repository'],
            'snapshot': target.relative_to(ROOT).as_posix(), **stats,
            'archive_sha256': sha256(archive) if archive.exists() else None,
            'license_note': source['license_note']}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify-only', action='store_true',
                        help='Check frozen snapshots offline; do not download or change work copies.')
    parser.add_argument('--reference-only', action='store_true',
                        help='Prepare only the pinned CSV needed for the repaired-controller proof.')
    args = parser.parse_args()
    if args.reference_only:
        prepare_reference(args.verify_only)
        return
    lock = ROOT / 'SOURCES.lock.json'
    sources = json.loads(lock.read_text())['sources']
    with concurrent.futures.ThreadPoolExecutor(max_workers=2) as executor:
        futures = [executor.submit(obtain, source, args.verify_only) for source in sources]
        records = [future.result() for future in futures]
    if args.verify_only:
        print('PASS: all original files match the pinned source manifest.')
        return
    for source, record in zip(sources, records):
        work = ROOT / 'work' / source['name']
        if work.exists():
            record['work_copy'] = 'Existing directory preserved without modification'
        else:
            shutil.copytree(ROOT / record['snapshot'], work)
            verify_tree(work, source)
            record['work_copy'] = 'Created and verified byte-identical to the snapshot'
    receipt = {'status': 'PASS',
               'timestamp_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
               'manifest_sha256': sha256(lock), 'sources': records,
               'scope': 'Source/data acquisition only; no dependency installation, training, repair, or new formal proof.'}
    (ROOT / 'INPUTS.local.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print('Ready: upstream/ contains originals; work/ contains editable copies.')


if __name__ == '__main__':
    main()
