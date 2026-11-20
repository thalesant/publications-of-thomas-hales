#!/usr/bin/env python3
"""Check fixed distribution files against both shipped SHA-256 manifests.

Run from any directory. This reads files only; it does not start mathematics,
rewrite hashes, or validate generated execution records (use confirm.py for that).
Additional files under runs/ and verification/ are expected after execution.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
SHA = re.compile(r"[0-9a-f]{64}\Z")

def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(1024**2), b''):
            h.update(block)
    return h.hexdigest()

def valid_name(name: str) -> bool:
    p = PurePosixPath(name)
    return (bool(name) and not p.is_absolute() and '\\' not in name and
            all(part not in {'', '.', '..'} for part in name.split('/')))

def verify(root: Path) -> tuple[int, list[str]]:
    root = root.resolve()
    errors: list[str] = []
    manifest = json.loads((root/'MANIFEST.json').read_text(encoding='utf-8'))
    expected = manifest.get('files')
    if not isinstance(expected, dict) or not expected:
        raise ValueError('MANIFEST.json has no fixed-file inventory')
    lines = (root/'SHA256SUMS').read_text(encoding='utf-8').splitlines()
    sums: dict[str, str] = {}
    for line in lines:
        if not line.strip():
            continue
        match = re.fullmatch(r'([0-9a-f]{64})  (.+)', line)
        if not match or not valid_name(match[2]):
            raise ValueError('Malformed SHA256SUMS line: ' + line)
        if match[2] in sums:
            raise ValueError('Duplicate SHA256SUMS entry: ' + match[2])
        sums[match[2]] = match[1]
    # The text manifest also identifies the JSON manifest itself. Neither
    # manifest hashes itself, so there is no circular digest dependency.
    manifest_digest = sums.pop('MANIFEST.json', None)
    if manifest_digest != digest(root/'MANIFEST.json'):
        errors.append('SHA256SUMS does not match MANIFEST.json')
    if sums != expected:
        errors.append('MANIFEST.json and SHA256SUMS fixed-file inventories differ')
    for name, sha in expected.items():
        if not isinstance(name, str) or not valid_name(name) or not isinstance(sha, str) or not SHA.fullmatch(sha):
            errors.append('Invalid manifest entry: ' + repr(name))
            continue
        path = root/name
        if path.is_symlink() or any(p.is_symlink() for p in path.parents if p != root and p.is_relative_to(root)):
            errors.append('Symlink is not a fixed release file: ' + name)
        elif not path.is_file():
            errors.append('Missing file: ' + name)
        elif digest(path) != sha:
            errors.append('Changed file: ' + name)
    return len(expected), errors

def main(argv=None) -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root', type=Path, default=ROOT, help='Package root (default: the directory containing this script’s parent scripts/ directory)')
    a = p.parse_args(argv)
    try:
        count, errors = verify(a.root)
        if errors:
            for error in errors:
                print('FAIL: ' + error, file=sys.stderr)
            return 1
        print(f'RELEASE FILES PASS: {count} fixed files and both manifests match.')
        print('No calculations were run. Generated execution records are checked by confirm.py.')
        return 0
    except (OSError, ValueError, TypeError) as ex:
        print('Release check failed: ' + str(ex), file=sys.stderr)
        return 1

if __name__ == '__main__':
    raise SystemExit(main())
