"""Optional standalone Tectonic build; outputs go to .local, never the snapshot.
Uses an existing Tectonic executable. Does not install or download a TeX runtime.
"""
from pathlib import Path
import argparse, shutil, subprocess, tempfile
ROOT=Path(__file__).resolve().parents[1]
def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--tectonic',default='tectonic')
    p.add_argument('--allow-resource-download',action='store_true',help='Allow existing Tectonic to fetch missing resource files; default cached files only.')
    a=p.parse_args();base=ROOT/'.local';base.mkdir(exist_ok=True)
    run=Path(tempfile.mkdtemp(prefix='build-',dir=base))
    for rel in ('paper/manuscript.tex','docs/expert_brief.tex'):
        source=ROOT/rel;dest=run/source.name;shutil.copyfile(source,dest)
        cmd=[a.tectonic,'--untrusted','--keep-logs','--keep-intermediates']
        if not a.allow_resource_download:cmd+=['--only-cached']
        subprocess.run(cmd+[str(dest)],cwd=run,check=True)
    print('Built files in '+run.relative_to(ROOT).as_posix())
if __name__=='__main__':main()
