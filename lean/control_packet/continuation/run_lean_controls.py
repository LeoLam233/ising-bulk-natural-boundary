#!/usr/bin/env python3
"""Focused ordinary proof controls. Run only under the coordinator's compile lease."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import sys
import time
import uuid

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent


def classify_result(filename, expected_failure, expected_lines, exit_code, stdout, stderr):
    combined = stdout + '\n' + stderr
    forbidden = re.search(r'unknown module|does not exist|unknown constant|unknown tactic|'
                          r'failed to load|invalid import|maximum.*memory|out of memory|heartbeats|'
                          r'maximum recursion|deterministic timeout|stack overflow|interrupted',
                          combined, re.IGNORECASE)
    errors = re.findall(r'^(.+?):(\d+):(\d+): error: (.*)$', combined, re.MULTILINE)
    if expected_failure is None:
        passed = exit_code == 0 and not errors and not forbidden
    else:
        correct_location = bool(errors) and all(
            Path(path).name == filename and int(line) in expected_lines
            for path, line, _column, _message in errors)
        correct_failure = any(re.search(expected_failure, message, re.IGNORECASE)
                              for _path, _line, _column, message in errors)
        passed = exit_code == 1 and correct_location and correct_failure and not forbidden and not stderr
    return bool(passed), errors


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean-bin-dir', type=Path, required=True)
    args = parser.parse_args()
    for executable in ('lake', 'lean'):
        path = args.lean_bin_dir / executable
        if not path.is_file() or not os.access(path, os.X_OK):
            parser.error('Missing executable: ' + str(path))
    run = HERE / 'results' / ('lean-' + datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')
                             + '-' + uuid.uuid4().hex[:8])
    run.mkdir(parents=True, exist_ok=False)
    sys.path.insert(0, str(ROOT / 'tools/continuation'))
    from preflight import clean_environment, snapshot
    env = clean_environment(args.lean_bin_dir)
    env['LEAN_NUM_THREADS'] = '1'
    initial_context = snapshot(ROOT, args.lean_bin_dir)
    cases = [
        ('PositiveArithmetic.lean', None),
        ('PositiveInterfaces.lean', None),
        ('InvalidArithmetic.lean', r"Tactic [`'‘]?rfl[`'’]? failed"),
        ('InvalidStrictWindow.lean', r'Type mismatch'),
        ('InvalidCancellation.lean', r'unsolved goals'),
    ]
    records = []
    for filename, expected_failure in cases:
        fixture = HERE / 'fixtures' / filename
        source = fixture.read_text()
        # Diagnostics must point at the marked mathematical proof/declaration.
        expected_lines = [index + 2 for index, line in enumerate(source.splitlines())
                          if 'EXPECT_FAILURE_HERE:' in line or 'EXPECT_FAILURE_DECLARATION:' in line]
        relative = fixture.relative_to(ROOT).as_posix()
        argv = [str(args.lean_bin_dir / 'lake'), '-f', 'lakefile.toml', 'env',
                str(args.lean_bin_dir / 'lean'), '-j1',
                '-DwarningAsError=true', relative]
        started = time.monotonic()
        process = subprocess.Popen(argv, cwd=ROOT, env=env, text=True, stdout=subprocess.PIPE,
                                   stderr=subprocess.PIPE, start_new_session=True)
        try:
            stdout, stderr = process.communicate(timeout=240)
            exit_code = process.returncode
        except subprocess.TimeoutExpired:
            # Terminate only this runner-created process group, including Lean
            # if Lake is still its parent. Do not leave a hidden compile lane.
            os.killpg(process.pid, signal.SIGTERM)
            try:
                stdout, stderr = process.communicate(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                stdout, stderr = process.communicate()
            exit_code = 'TIMEOUT'
        passed, errors = classify_result(filename, expected_failure, expected_lines,
                                         exit_code, stdout, stderr)
        record = {'fixture': filename, 'control_pass': bool(passed), 'argv': argv,
                  'fixture_sha256': hashlib.sha256(fixture.read_bytes()).hexdigest(),
                  'exit_code': exit_code, 'elapsed_seconds': time.monotonic() - started,
                  'expected_failure_pattern': expected_failure,
                  'expected_diagnostic_lines': expected_lines, 'parsed_errors': errors}
        stem = fixture.stem
        (run / (stem + '.stdout.txt')).write_text(stdout)
        (run / (stem + '.stderr.txt')).write_text(stderr)
        (run / (stem + '.result.json')).write_text(json.dumps(record, indent=2) + '\n')
        records.append(record)
        if not passed:
            break
    final_context = snapshot(ROOT, args.lean_bin_dir)
    identity_keys = ('PROOF_CRITICAL_PAYLOAD_ID', 'VERIFICATION_INPUT_ID', 'RUNTIME_ID')
    context_unchanged = all(initial_context[k] == final_context[k] for k in identity_keys)
    summary = {'context': {k: initial_context[k] for k in identity_keys},
               'context_unchanged': context_unchanged,
               'scope': 'ordinary positive and intentional-invalid focused proof controls only',
               'formal_audit': False, 'all_controls_pass': context_unchanged and len(records) == len(cases)
               and all(r['control_pass'] for r in records), 'case_count': len(records),
               'results_directory': str(run), 'cases': records}
    (run / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps({k: v for k, v in summary.items() if k != 'cases'}, indent=2))
    return 0 if summary['all_controls_pass'] else 1


if __name__ == '__main__':
    sys.exit(main())
