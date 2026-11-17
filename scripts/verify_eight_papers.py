#!/usr/bin/env python3
"""Check the live collection and the frozen evidence for earlier publications."""

import argparse
import hashlib
from io import BytesIO
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
BASE = '923266754afd65f5922a51f59a72ca56e1a88942'
# Last accepted eight-paper edition before F002, including the later editorial revisions.
SNAPSHOT = '7a7466eed439889bde2e981eb649b8bf8550eba8'
ARCHIVE = 'archive/manuscripts/pre-eight-2026-10-30'
MIGRATION = 'provenance/eight-papers-2026-10-30'
PREFIX = ARCHIVE + '/'
RECORD = MIGRATION + '/MIGRATION.json'
MANUSCRIPT_HASHES = 'papers/MANUSCRIPT_SHA256.json'
F002_ARCHIVE = 'archive/manuscripts/aniso-f002'
F002_PAPER_HASHES = {
    'ANISO_PSER_F002_FROZEN_52P.pdf': 'b82149625b7c2223c743b8e7482f4818543a760b46decd845acdf217d7a2376c',
    'ANISO_PSER_F002_FROZEN_52P.tex': '7c0fc588a688869d0c95698ec67b989bf644f3bd0cb9ca1c7eb8624d3976c977',
}
F002_SOURCE_MANIFEST = F002_ARCHIVE + '/FROZEN_SOURCE_SHA256.json'
F002_MANIFEST_SHA256 = '733133418727513bacbfa57161c1e964e2f28676de6f83dab688070419d26730'
STATUS = 'docs/eight-papers/EIGHT_PAPER_FORMALIZATION_STATUS.md'
CORRESPONDENCE = 'docs/eight-papers/LEAN_CORRESPONDENCE.md'
FROZEN_PREFIXES = ('lean/', 'verification/', 'provenance/', 'release/', 'audits/', 'research-history/')
FROZEN_MANIFESTS = {
    'ANISO_C001_OVERLAY_MANIFEST.json', 'HT_1747_OVERLAY_MANIFEST.json',
    'JOINT_C002_OVERLAY_MANIFEST.json', 'MANIFEST.json',
}


def require(ok, message):
    if not ok:
        raise SystemExit(f'Publication verification: {message}')


def git(*args, data=None):
    return subprocess.check_output(
        ['git', '-c', 'safe.directory=' + ROOT.as_posix(), '-C', str(ROOT), *args],
        input=data,
    )


def entries(ref, *paths):
    return {
        path.decode('utf8'): info.split()[2].decode('ascii')
        for line in git('ls-tree', '-rz', ref, '--', *paths).split(b'\0') if line
        for info, path in [line.split(b'\t', 1)]
    }


def git_blobs(ref, paths):
    """Read historical blobs in one Git process, retaining byte boundaries."""
    paths = list(paths)
    data = BytesIO(git('cat-file', '--batch', data=''.join(f'{ref}:{p}\n' for p in paths).encode()))
    for path in paths:
        header = data.readline().split()
        require(len(header) == 3 and header[1] == b'blob', f'missing historical blob: {ref}:{path}')
        size = int(header[2])
        value = data.read(size)
        require(len(value) == size and data.read(1) == b'\n', f'invalid Git blob response: {path}')
        yield path, value


def checked_file(rel, expected):
    p = ROOT / rel
    require(p.is_file() and not p.is_symlink(), f'missing or linked frozen file: {rel}')
    raw = p.read_bytes()
    blob = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
    require(blob == expected, f'frozen file changed: {rel}')
    return raw


def checked_sha256_file(rel, expected):
    p = ROOT / rel
    require(p.is_file() and not p.is_symlink(), f'missing or linked file: {rel}')
    raw = p.read_bytes()
    require(hashlib.sha256(raw).hexdigest() == expected, f'SHA-256 mismatch: {rel}')
    return raw


def check_sealed_tree(directory, snapshot):
    tree = ROOT / directory
    require(tree.is_dir() and not tree.is_symlink(), f'missing or linked frozen tree: {directory}')
    files = set()
    for p in tree.rglob('*'):
        rel = p.relative_to(ROOT).as_posix()
        require(not p.is_symlink(), f'linked archive entry: {rel}')
        if p.is_file():
            files.add(rel)
    expected = {rel for rel in snapshot if rel.startswith(directory + '/')}
    require(files == expected, f'frozen tree inventory changed: {sorted(files ^ expected)}')
    for rel in expected:
        checked_file(rel, snapshot[rel])


def verify_history():
    old = entries(BASE)
    snapshot = entries(SNAPSHOT, ARCHIVE, MIGRATION, 'docs/eight-papers')
    check_sealed_tree(ARCHIVE, snapshot)
    check_sealed_tree(MIGRATION, snapshot)
    m = json.loads((ROOT / RECORD).read_bytes())
    require(m['base'] == BASE and m['archive_prefix'] == PREFIX, 'incorrect migration baseline')
    require(len(old) == 4009, 'incomplete migration baseline')

    papers = {p: blob for p, blob in old.items() if p.startswith('paper/')}
    require(len(papers) == 67 and not (ROOT / 'paper').exists(), 'invalid former paper/ inventory')
    require({p for p in snapshot if p.startswith(PREFIX + 'paper/')} ==
            {PREFIX + p for p in papers}, 'incomplete historical manuscript archive')
    for rel, blob in papers.items():
        require(snapshot[PREFIX + rel] == blob, f'migration altered archived bytes: {rel}')

    # Reuse the six earlier formal acceptances only while their actual inputs match.
    # README.md is the live Lean entrance; the old copy remains in BASE.
    protected = {
        p: blob for p, blob in old.items()
        if (p.startswith(FROZEN_PREFIXES) or p in FROZEN_MANIFESTS) and p != 'lean/README.md'
    }
    for rel, blob in protected.items():
        checked_file(rel, blob)
    for rel, blob in snapshot.items():
        if rel.startswith('docs/eight-papers/') and rel not in {STATUS, CORRESPONDENCE}:
            checked_file(rel, blob)

    # Compare the dated record to its own editions, not to today's navigation or TeX.
    allowed = m['navigation_and_routing_changes']
    recorded = m['current_pairs']
    for rel, raw in git_blobs(SNAPSHOT, [*allowed, *recorded]):
        if rel in recorded:
            require(hashlib.sha256(raw).hexdigest() == recorded[rel]['sha256'],
                    f'historical edition hash disagrees: {rel}')
            continue
        row = allowed[rel]
        require(hashlib.sha256(raw).hexdigest() == row['new_sha256'],
                f'historical routing hash disagrees: {rel}')
        prev = m['historical_navigation_prefix'] + '/' + rel
        before = (ROOT / prev).read_bytes()
        require(snapshot[prev] == old[rel] and hashlib.sha256(before).hexdigest() == row['old_sha256'],
                f'archived original routing disagrees: {rel}')
        if rel.startswith('scripts/'):
            require(raw.decode('utf8').replace(row['routing_insertion'], '', 1) == before.decode('utf8'),
                    f'historical validator core changed during migration: {rel}')
    return m, len(protected)


def verify_f002():
    for name, digest in F002_PAPER_HASHES.items():
        checked_sha256_file(f'{F002_ARCHIVE}/{name}', digest)
    hashes = json.loads(checked_sha256_file(F002_SOURCE_MANIFEST, F002_MANIFEST_SHA256))
    require(len(hashes) == 4267, 'incorrect F002 source inventory')
    for rel, digest in hashes.items():
        checked_sha256_file(rel, digest)
    return len(hashes)


def verify():
    m, protected = verify_history()
    current = {p.relative_to(ROOT).as_posix() for p in (ROOT / 'papers').rglob('*')
               if p.suffix in {'.tex', '.pdf'}}
    require(current == set(m['current_pairs']) and len(current) == 16,
            'the current collection must have eight TeX/PDF pairs at the indexed paths')
    hashes = json.loads((ROOT / MANUSCRIPT_HASHES).read_bytes())
    require(isinstance(hashes, dict) and set(hashes) == current,
            'manuscript hashes must cover all eight TeX/PDF pairs')
    for rel in sorted(current):
        raw = checked_sha256_file(rel, hashes[rel])
        if rel.endswith('.tex'):
            source = raw.decode('utf8')
            require(source.count('ChatGPT') == 1 and 'Dehao Lin' in source,
                    f'author metadata or disclosure missing: {rel}')
        else:
            require(raw.startswith(b'%PDF-'), f'invalid PDF header: {rel}')
    f002_sources = verify_f002()

    # Follow the live navigation files, including the current formalization maps.
    live = sorted(set(m['live_markdown']) | {STATUS, CORRESPONDENCE, 'lean/README.md',
                  'docs/aniso-f002/PUBLICATION.md'})
    bad = []
    for rel in live:
        p = ROOT / rel
        source = p.read_text(encoding='utf8')
        for target in re.findall(r'!?\[[^\]]*\]\(([^)]+)\)', source):
            target = target.strip().split(' "', 1)[0].split('#', 1)[0]
            if not target or re.match(r'^[a-zA-Z][a-zA-Z0-9+.-]*:', target):
                continue
            if not (p.parent / target.replace('%20', ' ')).resolve().exists():
                bad.append((rel, target))
    require(not bad, f'broken current links: {bad}')
    print(json.dumps({'status': 'PASS', 'historical_snapshot': SNAPSHOT, 'archived_manuscript_files': 67,
                      'protected_baseline_files': protected, 'current_tex_pdf_files': len(current),
                      'f002_accepted_source_files': f002_sources}, indent=2))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--historical-checks', action='store_true')
    args = parser.parse_args()
    verify()
    if args.historical_checks:
        from eight_paper_paths import historical_root
        view = historical_root(ROOT, already_verified=True, link_packages=False)
        env = dict(os.environ, PYTHONUTF8='1')
        subprocess.run([sys.executable, str(view / 'scripts/verify_ht22_preservation.py')],
                       cwd=view, env=env, check=True)


if __name__ == '__main__':
    main()
