"""Check this snapshot's exact file inventory and SHA-256 content hashes.
No mathematical correctness or publisher identity is certified by this script.
"""
from pathlib import Path, PurePosixPath
import json, hashlib, sys
ROOT=Path(__file__).resolve().parents[1]
EXCLUDED={'MANIFEST.json'}
IGNORED_DIRS={'.git','.local','__pycache__','.venv'}
def main():
    manifest=ROOT/'MANIFEST.json'
    if not manifest.is_file():
        print('FAIL: MANIFEST.json missing');return 1
    data=json.loads(manifest.read_text(encoding='utf-8'))
    rows=data['files'];expected={};errors=[]
    for row in rows:
        rel=row['path'];p=PurePosixPath(rel)
        if p.is_absolute() or '..' in p.parts or '\\' in rel or ':' in rel or rel in expected:
            errors.append('Unsafe or duplicate manifest path: '+rel);continue
        expected[rel]=row
        target=ROOT.joinpath(*p.parts)
        if not target.is_file() or target.is_symlink():errors.append('Missing/unsupported file: '+rel);continue
        content=target.read_bytes()
        if len(content)!=row['bytes'] or hashlib.sha256(content).hexdigest()!=row['sha256']:errors.append('Hash/size mismatch: '+rel)
    actual={p.relative_to(ROOT).as_posix() for p in ROOT.rglob('*') if p.is_file() and not any(x in IGNORED_DIRS for x in p.relative_to(ROOT).parts) and p.relative_to(ROOT).as_posix() not in EXCLUDED}
    for rel in sorted(actual-set(expected)):errors.append('Unlisted file: '+rel)
    for e in errors:print(e)
    print(json.dumps({'status':'FILE_INTEGRITY_OK' if not errors else 'FILE_INTEGRITY_FAILED','files':len(expected),'errors':len(errors),'manifest_self_hashed':False,'mathematics_verified':False}))
    return 1 if errors else 0
if __name__=='__main__':sys.exit(main())
