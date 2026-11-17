#!/usr/bin/env python3
"""Route publication checks using the complete Git diff, including large overlays."""

import argparse
import os
from pathlib import PurePosixPath
import subprocess


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('event', choices=['pull_request', 'push', 'workflow_dispatch'])
    parser.add_argument('base')
    parser.add_argument('head')
    args = parser.parse_args()

    # Manual dispatch runs both; a missing push predecessor is conservatively broad.
    full = args.event == 'workflow_dispatch'
    paths = []
    if not full:
        mode = '...' if args.event == 'pull_request' else '..'
        diff = subprocess.run(
            ['git', 'diff', '--name-only', '--no-renames', '-z', args.base + mode + args.head, '--'],
            stdout=subprocess.PIPE,
        )
        if args.event == 'pull_request':
            diff.check_returncode()
        full = diff.returncode != 0
        paths = [os.fsdecode(p) for p in diff.stdout.split(b'\0') if p]

    papers = full or any(
        (p.startswith('papers/') and PurePosixPath(p).suffix != '.md')
        or p == 'scripts/build_current_papers.py'
        for p in paths
    )
    # Old shared Lean sources and pins are checked by publication integrity.
    # Run the F002 build for PRs; the ordinary post-merge push rechecks integrity.
    f002 = args.event == 'workflow_dispatch' or (
        args.event == 'pull_request' and any(
            p.startswith('lean/IsingBulk/AnisoF002/')
            or p in {'lean/lakefile.toml', 'lean/lean-toolchain', 'lean/lake-manifest.json',
                     '.github/workflows/eight-paper-publication.yml', 'scripts/publication_ci_scope.py'}
            or (p.startswith('lean/') and PurePosixPath(p).parent == PurePosixPath('lean')
                and ('AnisoF002' in p or 'lakefile.aniso-f002' in p))
            for p in paths
        )
    )
    print(f'manuscripts={str(papers).lower()}\nf002={str(f002).lower()}')


if __name__ == '__main__':
    main()
