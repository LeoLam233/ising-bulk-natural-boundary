#!/usr/bin/env python3
"""Verify the exact frozen C001 additive overlay and all protected LT/HT bytes."""
from pathlib import Path
import hashlib,json,subprocess

ROOT=Path(__file__).resolve().parents[1]
SHA=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()

def verify():
    manifest=json.loads((ROOT/'ANISO_C001_OVERLAY_MANIFEST.json').read_text())
    assert manifest['resolved_base_commit']=='76c3ad5457e883cc15032fdf4205da23ceba58fe'
    assert manifest['nested_archive_sha256']=='0fd8e6d5e47df58c662f78a6855402aebe2e5fdd89343d63cb81cbe960317d6c'
    files=manifest['frozen_lean_files']
    assert len(files)==2279 and sum(p.endswith('.lean') for p in files)==2274
    assert sum(p.startswith('lean/IsingBulk/Anisotropic/') for p in files)==762
    assert len(manifest['shared_frozen_paths'])==1514
    assert len(manifest['additive_frozen_paths'])==765
    assert set(manifest['shared_frozen_paths']).isdisjoint(manifest['additive_frozen_paths'])
    assert set(manifest['shared_frozen_paths'])|set(manifest['additive_frozen_paths'])==set(files)
    for group in ['frozen_lean_files','protected_base_files','frozen_manuscripts','historical_publication_files']:
        for rel,expected in manifest[group].items():
            assert (ROOT/rel).is_file(),f'Missing {rel}'
            assert SHA(ROOT/rel)==expected,f'Protected/frozen byte mismatch: {rel}'
    assert (ROOT/'lean/lean-toolchain').read_text().strip()=='leanprover/lean4:v4.34.1'
    lock=json.loads((ROOT/'lean/lake-manifest.json').read_text())
    assert lock['packages']==manifest['dependencies'],'Dependency lock changed'
    assert next(p['rev'] for p in lock['packages'] if p['name']=='mathlib')=='d13f23b723b8a846827a245b89c10fc7d3f11612'
    actual={p.relative_to(ROOT).as_posix() for p in (ROOT/'lean/IsingBulk/Anisotropic').rglob('*') if p.is_file()}
    expected={p for p in files if p.startswith('lean/IsingBulk/Anisotropic/')}
    assert actual==expected,'Unexpected/missing file inside frozen ANISO namespace'
    # When history is available, confirm the protected snapshot against the actual base.
    base=manifest['resolved_base_commit']
    if subprocess.run(['git','cat-file','-e',base+'^{commit}'],cwd=ROOT,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode==0:
        rows=subprocess.check_output(['git','ls-tree','-r',base],cwd=ROOT).decode().splitlines()
        tree={row.split('\t',1)[1]:row.split()[2] for row in rows}
        for rel in manifest['protected_base_files']:
            assert rel in tree,f'Protected path absent from base: {rel}'
            data=(ROOT/rel).read_bytes()
            blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
            assert blob==tree[rel],f'Protected Git blob changed: {rel}'
    print(f'PASS: 2279 exact frozen files; 1514 shared; 765 additive; {len(manifest["protected_base_files"])} protected prior files; zero conflicts')
    return manifest

if __name__=='__main__': verify()
