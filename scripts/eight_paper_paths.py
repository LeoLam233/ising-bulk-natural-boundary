"""Materialize the immutable pre-migration tree for unchanged legacy validators."""

import tempfile
from pathlib import Path
import subprocess

_views = []


def historical_root(root, *, already_verified=False, link_packages=True):
    root = Path(root).resolve()
    if (root / 'paper').is_dir():
        return root
    from verify_eight_papers import BASE, verify
    if not already_verified:
        verify()

    tmp = tempfile.TemporaryDirectory(prefix='eight-paper-historical-')
    _views.append(tmp)
    target = Path(tmp.name) / 'repository'
    # Separate Git metadata and index; the source object database is read-only.
    subprocess.run(['git', 'init', '--quiet', str(target)], check=True)
    objects = subprocess.check_output(
        ['git', '-c', 'safe.directory=' + root.as_posix(), '-C', str(root),
         'rev-parse', '--git-path', 'objects'],
    ).decode().strip()
    objects = (root / objects).resolve()
    (target / '.git/objects/info/alternates').write_bytes((objects.as_posix() + '\n').encode('utf8'))
    cmd = ['git', '-c', 'safe.directory=' + target.as_posix(), '-c', 'core.autocrlf=false', '-C', str(target)]
    subprocess.run(cmd + ['read-tree', BASE], check=True)
    subprocess.run(cmd + ['update-ref', 'refs/heads/historical-view', BASE], check=True)
    subprocess.run(cmd + ['symbolic-ref', 'HEAD', 'refs/heads/historical-view'], check=True)
    subprocess.run(cmd + ['checkout-index', '--all'], check=True)
    packages = root / 'lean/.lake/packages'
    if link_packages and packages.is_dir():
        (target / 'lean/.lake').mkdir(exist_ok=True)
        (target / 'lean/.lake/packages').symlink_to(packages.resolve(), target_is_directory=True)
    return target
