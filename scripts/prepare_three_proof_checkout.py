#!/usr/bin/env python3
"""Create a fresh source worktree after upstream-cache preparation."""
from pathlib import Path
import argparse,json,subprocess

ROOT=Path(__file__).resolve().parents[1]
def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',required=True,type=Path)
    target=parser.parse_args().output.resolve()
    assert not target.exists(),'Fresh source checkout destination already exists'
    packages=ROOT/'lean/.lake/packages'
    assert packages.is_dir(),'Prepare the pinned upstream dependency cache first'
    # No root .lake/config or .lake/build file is copied. The unchanged strict
    # runner subsequently rejects every pre-existing candidate-project .olean.
    subprocess.run(['git','worktree','add','--detach',str(target),'HEAD'],cwd=ROOT,check=True)
    lake=target/'lean/.lake';lake.mkdir()
    (lake/'packages').symlink_to(packages.resolve(),target_is_directory=True)
    assert not list((lake/'build').rglob('*.olean'))
    assert not [p for p in (target/'lean').rglob('*.olean') if '.lake/packages' not in p.relative_to(target/'lean').as_posix()]
    print(json.dumps(dict(checkout=str(target),commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=target,text=True).strip(),project_olean_count=0,upstream_packages=str(packages.resolve()))))

if __name__=='__main__':main()
