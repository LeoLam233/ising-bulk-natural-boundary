#!/usr/bin/env python3
"""Execute unchanged historical validators with their exact pinned navigation context."""
import hashlib,json,pathlib,shutil,subprocess,sys,tempfile
ROOT=pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
from verify_lt22_publication import verify

def main():
    verify()
    # Current-tree exact source/configuration gate, without historical prose assumptions.
    subprocess.run([sys.executable,str(ROOT/'scripts/verify_four_result_publication.py'),'--source-only'],check=True)
    record=json.loads((ROOT/'provenance/lt22/HISTORICAL_NAVIGATION.json').read_text())
    old=json.loads((ROOT/'ANISO_C001_OVERLAY_MANIFEST.json').read_text())
    expected={r['path'] for r in record['files']}
    assert expected=={'high-temperature/README.md','high-temperature/README.zh.md','low-temperature/README.md','low-temperature/README.zh.md','paper/ht/README.md','paper/lt/README.md'}
    # This is the same historical-navigation-view convention used by the existing
    # three-result validator for HT's REPOSITORY_MAP.md. Never replace formal sources.
    with tempfile.TemporaryDirectory(prefix='lt22-preservation-') as tmp:
        view=pathlib.Path(tmp)/'repository'
        shutil.copytree(ROOT,view,ignore=shutil.ignore_patterns('.git','.lake','.local','__pycache__'))
        for row in record['files']:
            rel=row['path'];data=(ROOT/'provenance/lt22/historical-navigation'/rel).read_bytes()
            assert hashlib.sha256(data).hexdigest()==row['sha256']==old['protected_base_files'][rel]
            (view/rel).write_bytes(data)
        subprocess.run([sys.executable,str(view/'scripts/verify_four_result_publication.py')],check=True)
    print('PASS: current-tree source manifest plus unchanged historical publication validators; only six pinned navigation READMEs restored in temporary view')

if __name__=='__main__':main()
