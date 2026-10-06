#!/usr/bin/env python3
"""Run small isolated manifest controls, never edit the production payload."""
import copy
from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess
import sys
import uuid

from payload_manifest import digest, encode, snapshot

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
SOURCE = 'IsingBulk/Control.lean'
PIN = 'lean-toolchain'


def main():
    run = HERE / 'results' / ('manifest-' + datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')
                             + '-' + uuid.uuid4().hex[:8])
    run.mkdir(parents=True, exist_ok=False)
    original = {
        SOURCE: (HERE / 'fixtures/PositiveArithmetic.lean').read_bytes(),
        PIN: (ROOT / PIN).read_bytes(),
        'lakefile.toml': (ROOT / 'lakefile.toml').read_bytes(),
        'lake-manifest.json': (ROOT / 'lake-manifest.json').read_bytes(),
    }
    baseline = run / 'baseline'
    baseline.mkdir()
    for name, data in original.items():
        dest = baseline / name
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(data)
    manifest = snapshot(baseline)
    trusted_raw = encode(manifest)
    trusted_id = digest(trusted_raw)
    (run / 'trusted-manifest.json').write_bytes(trusted_raw)
    (run / 'trusted-id.txt').write_text(trusted_id + '\n')
    cases = []

    def add(name, *, payload=None, manifest_bytes=trusted_raw, test_pin=False,
            code=None, path=None):
        cases.append((name, original if payload is None else payload, manifest_bytes,
                      digest(manifest_bytes) if test_pin else trusted_id, code, path))

    add('positive_untouched')
    changed = dict(original)
    changed[SOURCE] = original[SOURCE][:-1] + b' '
    add('source_byte_tamper', payload=changed, code='SHA256_MISMATCH', path=SOURCE)
    changed_pin = dict(original)
    changed_pin[PIN] = original[PIN][:-1] + b' '
    add('toolchain_pin_byte_tamper', payload=changed_pin, code='SHA256_MISMATCH', path=PIN)
    add('missing_source', payload={k: v for k, v in original.items() if k != SOURCE},
        code='MISSING_FILE', path=SOURCE)
    add('undeclared_hidden_file', payload={**original, '.hidden-proof-input.txt': b'undeclared\n'},
        code='UNDECLARED_FILE', path='.hidden-proof-input.txt')
    bad_digest = copy.deepcopy(manifest)
    bad_digest['files'][0]['sha256'] = '0' * 64
    add('manifest_byte_tamper', manifest_bytes=encode(bad_digest), code='MANIFEST_ID_MISMATCH')
    add('bad_digest_with_test_pin', manifest_bytes=encode(bad_digest), test_pin=True,
        code='SHA256_MISMATCH', path=bad_digest['files'][0]['path'])
    omitted = copy.deepcopy(manifest)
    omitted['files'] = [entry for entry in omitted['files'] if entry['path'] != SOURCE]
    add('omitted_entry_with_test_pin', manifest_bytes=encode(omitted), test_pin=True,
        code='UNDECLARED_FILE', path=SOURCE)
    duplicate = copy.deepcopy(manifest)
    duplicate['files'].append(copy.deepcopy(duplicate['files'][0]))
    add('duplicate_entry_with_test_pin', manifest_bytes=encode(duplicate), test_pin=True,
        code='DUPLICATE_PATH', path=duplicate['files'][0]['path'])
    traversal = copy.deepcopy(manifest)
    traversal['files'][0]['path'] = '../outside.lean'
    add('traversal_entry_with_test_pin', manifest_bytes=encode(traversal), test_pin=True,
        code='UNSAFE_PATH', path='../outside.lean')
    coherent = copy.deepcopy(manifest)
    for entry in coherent['files']:
        if entry['path'] == SOURCE:
            entry['sha256'] = digest(changed[SOURCE])
    add('coherent_source_and_manifest_tamper', payload=changed, manifest_bytes=encode(coherent),
        code='MANIFEST_ID_MISMATCH')
    malformed = b'{invalid json\n'
    add('invalid_json_with_test_pin', manifest_bytes=malformed, test_pin=True,
        code='MANIFEST_PARSE_ERROR')
    repeated_key = b'{"schema":"x","schema":"y","files":[]}\n'
    add('duplicate_json_key_with_test_pin', manifest_bytes=repeated_key, test_pin=True,
        code='DUPLICATE_JSON_KEY', path='schema')

    records = []
    for name, payload, raw, expected_id, expected_code, expected_path in cases:
        directory = run / name
        staging = directory / 'payload'
        staging.mkdir(parents=True)
        for relative, data in payload.items():
            target = staging / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
        manifest_path = directory / 'manifest.json'
        manifest_path.write_bytes(raw)
        argv = [sys.executable, str(HERE / 'payload_manifest.py'), 'verify',
                '--payload-root', str(staging), '--manifest', str(manifest_path),
                '--expected-id', expected_id]
        result = subprocess.run(argv, text=True, capture_output=True, timeout=30)
        (directory / 'stdout.txt').write_text(result.stdout)
        (directory / 'stderr.txt').write_text(result.stderr)
        try:
            actual = json.loads(result.stdout)
        except json.JSONDecodeError:
            actual = {'status': 'UNPARSEABLE_OUTPUT'}
        if expected_code is None:
            passed = result.returncode == 0 and actual.get('status') == 'PASS'
        else:
            passed = (result.returncode == 1 and actual.get('status') == 'FAIL'
                      and actual.get('error_code') == expected_code
                      and actual.get('path') == expected_path)
        passed = passed and not result.stderr
        record = {'case': name, 'control_pass': passed, 'argv': argv,
                  'exit_code': result.returncode, 'expected_error_code': expected_code,
                  'expected_error_path': expected_path, 'actual': actual}
        (directory / 'result.json').write_text(json.dumps(record, indent=2) + '\n')
        records.append(record)
    summary = {'scope': 'isolated bounded-payload byte and inventory controls only',
               'formal_audit': False, 'all_controls_pass': all(r['control_pass'] for r in records),
               'case_count': len(records), 'trusted_manifest_id': trusted_id,
               'results_directory': str(run), 'cases': records}
    (run / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps({k: v for k, v in summary.items() if k != 'cases'}, indent=2))
    return 0 if summary['all_controls_pass'] else 1


if __name__ == '__main__':
    sys.exit(main())
