#!/usr/bin/env python3
"""Byte/inventory verifier for an explicitly staged, bounded proof payload.

This verifier does not decide which production files belong in a final payload.
The coordinator must establish that scope independently. Expected manifest IDs
must be supplied from the reviewed freeze receipt, not read from the manifest.
"""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys

SCHEMA = 'ising-bounded-payload-manifest-v1'


class VerificationFailure(Exception):
    def __init__(self, code, path=None):
        self.code, self.path = code, path
        super().__init__(code)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def inventory(root):
    if root.is_symlink() or not root.is_dir():
        raise VerificationFailure('INVALID_PAYLOAD_ROOT')
    result = {}
    for path in sorted(root.rglob('*')):
        relative = path.relative_to(root).as_posix()
        if path.is_symlink():
            raise VerificationFailure('SYMLINK_FORBIDDEN', relative)
        if path.is_file():
            result[relative] = path
        elif not path.is_dir():
            raise VerificationFailure('NONREGULAR_FILE', relative)
    return result


def snapshot(root):
    entries = []
    for name, path in inventory(root).items():
        data = path.read_bytes()
        entries.append({'path': name, 'bytes': len(data), 'sha256': digest(data)})
    return {'schema': SCHEMA, 'files': entries}


def encode(manifest):
    return (json.dumps(manifest, sort_keys=True, separators=(',', ':')) + '\n').encode()


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise VerificationFailure('DUPLICATE_JSON_KEY', key)
        result[key] = value
    return result


def verify(root, raw, expected_id):
    if not re.fullmatch('[0-9a-f]{64}', expected_id):
        raise VerificationFailure('INVALID_EXPECTED_ID')
    if digest(raw) != expected_id:
        raise VerificationFailure('MANIFEST_ID_MISMATCH')
    try:
        manifest = json.loads(raw, object_pairs_hook=unique_object)
    except (json.JSONDecodeError, UnicodeDecodeError):
        raise VerificationFailure('MANIFEST_PARSE_ERROR') from None
    if (not isinstance(manifest, dict) or set(manifest) != {'schema', 'files'}
            or manifest['schema'] != SCHEMA or not isinstance(manifest['files'], list)):
        raise VerificationFailure('MANIFEST_SCHEMA_ERROR')
    expected = {}
    for entry in manifest['files']:
        if not isinstance(entry, dict) or set(entry) != {'path', 'bytes', 'sha256'}:
            raise VerificationFailure('MANIFEST_ENTRY_ERROR')
        name = entry['path']
        if (not isinstance(name, str) or not name or '\\' in name or '\x00' in name
                or PurePosixPath(name).is_absolute() or PurePosixPath(name).as_posix() != name
                or any(part in ('', '.', '..') for part in name.split('/'))):
            raise VerificationFailure('UNSAFE_PATH', str(name))
        if name in expected:
            raise VerificationFailure('DUPLICATE_PATH', name)
        if (type(entry['bytes']) is not int or entry['bytes'] < 0
                or not isinstance(entry['sha256'], str)
                or not re.fullmatch('[0-9a-f]{64}', entry['sha256'])):
            raise VerificationFailure('MANIFEST_ENTRY_ERROR', name)
        expected[name] = entry
    actual = inventory(root)
    missing = sorted(set(expected) - set(actual))
    extra = sorted(set(actual) - set(expected))
    if missing:
        raise VerificationFailure('MISSING_FILE', missing[0])
    if extra:
        raise VerificationFailure('UNDECLARED_FILE', extra[0])
    for name, entry in expected.items():
        data = actual[name].read_bytes()
        if len(data) != entry['bytes']:
            raise VerificationFailure('BYTE_SIZE_MISMATCH', name)
        if digest(data) != entry['sha256']:
            raise VerificationFailure('SHA256_MISMATCH', name)
    return {'status': 'PASS', 'manifest_id': expected_id, 'file_count': len(expected)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    create = sub.add_parser('snapshot')
    create.add_argument('--payload-root', type=Path, required=True)
    create.add_argument('--manifest', type=Path, required=True)
    check = sub.add_parser('verify')
    check.add_argument('--payload-root', type=Path, required=True)
    check.add_argument('--manifest', type=Path, required=True)
    check.add_argument('--expected-id', required=True)
    args = parser.parse_args()
    try:
        if args.command == 'snapshot':
            if args.manifest.exists():
                raise VerificationFailure('OUTPUT_ALREADY_EXISTS')
            raw = encode(snapshot(args.payload_root))
            args.manifest.write_bytes(raw)
            result = {'status': 'SNAPSHOT_CREATED', 'manifest_id': digest(raw)}
        else:
            result = verify(args.payload_root, args.manifest.read_bytes(), args.expected_id)
    except VerificationFailure as error:
        print(json.dumps({'status': 'FAIL', 'error_code': error.code, 'path': error.path}))
        return 1
    except OSError as error:
        print(json.dumps({'status': 'HARNESS_ERROR', 'error': str(error)}))
        return 2
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == '__main__':
    sys.exit(main())
