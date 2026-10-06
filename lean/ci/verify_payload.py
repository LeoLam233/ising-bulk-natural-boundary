"""Verify proof bytes against a distinct caller-supplied payload identity."""
import argparse
import hashlib
import json
import os
import pathlib
import re
import subprocess
import sys

root = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0, str(root / 'tools/continuation'))
from preflight import PreflightError, check_dependency_source, reject_dependency_project_namespaces


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--expected-id', required=True,
                        help='Expected proof ID from the caller, not from payload.json')
    parser.add_argument('--dependencies', action='store_true')
    args = parser.parse_args()
    if not re.fullmatch('[0-9a-f]{64}', args.expected_id):
        raise SystemExit('Expected ID must be a SHA-256 digest')
    data = json.loads((root / 'ci/payload.json').read_text())
    expected = data['proof_inputs']
    actual = dict(expected)
    actual['files'] = {}
    for name, digest in expected['files'].items():
        path = root / name
        if not path.is_file() or path.is_symlink():
            raise SystemExit('Missing or linked payload: ' + name)
        actual['files'][name] = hashlib.sha256(path.read_bytes()).hexdigest()
        if actual['files'][name] != digest:
            raise SystemExit('Payload changed: ' + name)
    production = {p.relative_to(root).as_posix() for p in (root / 'IsingBulk').rglob('*.lean')} | {'IsingBulk.lean'}
    if production != {p for p in expected['files'] if p.endswith('.lean')}:
        raise SystemExit('Production inventory changed')
    identity = hashlib.sha256(json.dumps(actual, sort_keys=True, separators=(',', ':'),
                                        ensure_ascii=False).encode()).hexdigest()
    if identity != args.expected_id or identity != data['PROOF_CRITICAL_PAYLOAD_ID']:
        raise SystemExit('Identity mismatch against caller-supplied expected ID')
    if (root / 'lakefile.lean').exists():
        raise SystemExit('Unexpected alternate Lake configuration')
    if args.dependencies:
        reject_dependency_project_namespaces(root)
        for dep in expected['dependencies']:
            check_dependency_source(root / '.lake/packages' / dep['name'], dep['revision'], dict(os.environ))
    print('PAYLOAD_IDENTITY_PASS', identity, 'production_files', len(production))
    return 0


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (PreflightError, OSError, ValueError, KeyError, subprocess.SubprocessError) as exc:
        raise SystemExit('PAYLOAD_IDENTITY_FAILED: ' + str(exc))
