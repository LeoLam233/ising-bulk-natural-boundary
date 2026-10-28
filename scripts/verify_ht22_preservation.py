#!/usr/bin/env python3
"""Run unchanged LT22/four/three-result validators in a hash-bound historical view."""
import hashlib,json,pathlib,shutil,subprocess,sys,tempfile
from verify_ht22_publication import ROOT,verify,read,sha
def main():
    verify()
    edits=read('provenance/ht22/PUBLICATION_ALLOWLIST.json')['files']
    with tempfile.TemporaryDirectory(prefix='ht22-historical-') as tmp:
        view=pathlib.Path(tmp)/'repository'
        shutil.copytree(ROOT,view,ignore=shutil.ignore_patterns('.git','.lake','.local','__pycache__'))
        for rel,row in edits.items():
            data=(ROOT/'provenance/ht22/historical-navigation'/rel).read_bytes()
            assert hashlib.sha256(data).hexdigest()==row['old_sha256']
            (view/rel).write_bytes(data)
        subprocess.run([sys.executable,str(view/'scripts/verify_lt22_preservation.py')],check=True)
    print('PASS: current-tree HT22/baseline identity and unchanged LT22/four/three-result validators; publication navigation restored only in temporary verified view')
if __name__=='__main__':main()
