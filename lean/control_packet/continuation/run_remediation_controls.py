#!/usr/bin/env python3
"""Focused R1/R3/R4 regressions against the production payload verifier."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import uuid

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--shadow-tree', type=Path,
                        help='Optional compiled mutant IsingBulk tree for the audited attack')
    args = parser.parse_args()
    expected_id = json.loads((ROOT / 'ci/accepted_identity.json').read_text())['PROOF_CRITICAL_PAYLOAD_ID']
    run = HERE / 'results' / ('remediation-' + datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')
                             + '-' + uuid.uuid4().hex[:8])
    staging = run / 'payload/lean'
    staging.mkdir(parents=True)
    payload_bytes = (ROOT / 'ci/payload.json').read_bytes()
    payload = json.loads(payload_bytes)
    names = set(payload['proof_inputs']['files']) | {'ci/payload.json', 'ci/verify_payload.py',
                                                   'tools/continuation/preflight.py'}
    for name in sorted(names):
        destination = staging / name
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes((ROOT / name).read_bytes())
    records = []
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE='1')

    def check(name, diagnostic=None, dependencies=False):
        argv = [sys.executable, '-B', str(staging / 'ci/verify_payload.py'), '--expected-id', expected_id]
        if dependencies:
            argv.append('--dependencies')
        result = subprocess.run(argv, cwd=staging, env=env, text=True, capture_output=True, timeout=120)
        (run / (name + '.stdout.log')).write_text(result.stdout)
        (run / (name + '.stderr.log')).write_text(result.stderr)
        passed = (result.returncode == 0 and 'PAYLOAD_IDENTITY_PASS ' + expected_id in result.stdout) \
            if diagnostic is None else (result.returncode == 1 and diagnostic in result.stderr)
        record = dict(case=name, passed=passed, exit_code=result.returncode,
                      expected_diagnostic=diagnostic, argv=argv)
        records.append(record)
        print(json.dumps(record), flush=True)
        if not passed:
            raise RuntimeError('Unexpected production verifier result: ' + name)

    check('positive_untouched')
    source_name = 'IsingBulk/Final/UnconditionalNaturalBoundary.lean'
    source_path = staging / source_name
    original_source = source_path.read_bytes()
    source_path.write_bytes(original_source + b'\n-- coherent payload tamper regression\n')
    mutant = json.loads(payload_bytes)
    mutant['proof_inputs']['files'][source_name] = hashlib.sha256(source_path.read_bytes()).hexdigest()
    mutant['PROOF_CRITICAL_PAYLOAD_ID'] = hashlib.sha256(json.dumps(mutant['proof_inputs'],
        sort_keys=True, separators=(',', ':'), ensure_ascii=False).encode()).hexdigest()
    (staging / 'ci/payload.json').write_text(json.dumps(mutant, indent=2) + '\n')
    check('coherent_source_and_manifest_tamper', 'Identity mismatch against caller-supplied expected ID')
    source_path.write_bytes(original_source)
    (staging / 'ci/payload.json').write_bytes(payload_bytes)

    packages = staging / '.lake/packages'
    packages.mkdir(parents=True)
    for dep in payload['proof_inputs']['dependencies']:
        source = ROOT / '.lake/packages' / dep['name']
        destination = packages / dep['name']
        if dep['name'] in ('Cli', 'plausible'):
            shutil.copytree(source, destination, ignore=shutil.ignore_patterns('.lake'))
        else:
            destination.symlink_to(source.resolve(), target_is_directory=True)
    check('positive_dependencies', dependencies=True)
    cli = packages / 'Cli'
    pinned = next(dep['revision'] for dep in payload['proof_inputs']['dependencies'] if dep['name'] == 'Cli')

    def git(*args):
        return subprocess.check_output(['git', '-C', str(cli), *args], text=True, env=env).strip()

    previous = git('rev-parse', 'HEAD~1')
    git('checkout', '--quiet', '--detach', previous)
    check('wrong_dependency_HEAD', 'Dependency pin/source mismatch: Cli', dependencies=True)
    git('checkout', '--quiet', '--detach', pinned)
    tracked = git('ls-tree', '-r', '--name-only', 'HEAD').splitlines()
    tracked_name = next(name for name in tracked if name.endswith('.md'))
    tracked_path = cli / tracked_name
    tracked_bytes = tracked_path.read_bytes()
    tracked_path.write_bytes(tracked_bytes + b'\nTracked dependency tamper.\n')
    check('dirty_tracked_dependency', 'Dependency pin/source mismatch: Cli', dependencies=True)
    tracked_path.write_bytes(tracked_bytes)
    override = cli / 'lakefile.lean'
    if override.exists():
        raise RuntimeError('The audited Cli override control requires the pinned TOML-only configuration')
    override.write_text('-- untracked Lake override regression\n')
    check('untracked_Lake_override', 'Unbound dependency configuration: Cli/lakefile.lean', dependencies=True)
    override.unlink()

    build = packages / 'plausible/.lake/build/lib/lean'
    build.mkdir(parents=True)
    for name in ('IsingBulk', 'IsingBulk.olean', 'Audit', 'Audit.olean'):
        target = build / name
        if '.' in name:
            target.write_bytes(b'foreign artifact rejected before loading\n')
        else:
            target.mkdir()
        check('shadow_' + name.replace('.', '_'), 'Foreign project namespace in dependency build:', dependencies=True)
        if target.is_dir():
            target.rmdir()
        else:
            target.unlink()
    if args.shadow_tree:
        tree = args.shadow_tree.resolve()
        if tree.name != 'IsingBulk' or not tree.is_dir() or not tree.with_suffix('.olean').is_file():
            raise RuntimeError('Expected a complete compiled IsingBulk tree and adjacent root olean')
        (build / 'IsingBulk').symlink_to(tree, target_is_directory=True)
        (build / 'IsingBulk.olean').symlink_to(tree.with_suffix('.olean'))
        check('audited_complete_mutant_tree', 'Foreign project namespace in dependency build:', dependencies=True)
        (build / 'IsingBulk').unlink()
        (build / 'IsingBulk.olean').unlink()
    check('positive_restored_dependencies', dependencies=True)
    summary = dict(all_controls_pass=all(record['passed'] for record in records), case_count=len(records),
                   expected_id=expected_id, source_payload_id=payload['PROOF_CRITICAL_PAYLOAD_ID'], cases=records,
                   scope='Targeted production verifier regressions; no build or kernel replay')
    (run / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps({k: v for k, v in summary.items() if k != 'cases'}, indent=2))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
