#!/usr/bin/env python3
"""Fail-closed immutable HT22 source, inventory, preservation and routing gate."""
import argparse,fnmatch,hashlib,json,pathlib,re,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def read(rel):return json.loads((ROOT/rel).read_text(encoding='utf-8'))
def verify(source_bundle=False):
    identity=read('provenance/ht22/SOURCE_IDENTITY.json')
    baseline=read('provenance/ht22/PROTECTED_BASELINE.json')
    frozen=read('provenance/ht22/FROZEN_SOURCE_MANIFEST.json')['files']
    assert sha(ROOT/'provenance/ht22/FROZEN_SOURCE_MANIFEST.json')=='a0c4ddb4725a86382ee8f57e1e81b25cf60b8a2e1469d165c9efa395a65d227f'
    assert len(frozen)==4151 and len(baseline['files'])==3575
    assert sha(ROOT/'provenance/ht22/PROTECTED_BASELINE.json')==frozen['PROTECTED_BASELINE.json']['sha256']
    assert baseline['commit']=='465375f2b6cc0952adaca87eddc859a40f577748'
    for rel,wanted in identity['files'].items():
        p=ROOT/rel
        assert p.is_file() and not p.is_symlink() and sha(p)==wanted,('Frozen/source input changed',rel)
        if rel.startswith('lean/'):
            assert wanted==frozen['repository/'+rel]['sha256'],('Noncanonical formal/config input',rel)
    modules={p.relative_to(ROOT).as_posix() for p in (ROOT/'lean/IsingBulk/HT22').rglob('*') if p.is_file()}
    expected={p for p in identity['frozen_additions'] if p.startswith('lean/IsingBulk/HT22/')}
    assert modules==expected and len(modules)==378,('HT22 inventory differs',sorted(modules^expected))
    for rel in identity['frozen_additions']:
        assert sha(ROOT/rel)==frozen['repository/'+rel]['sha256'],rel
    for ext,expected_sha in [('pdf','2e0e674c88f3bd5edc3846aa1f62eb2a124ce96c588221b24cc176f2a97a00d9'),('tex','5d962d44180f33df66fbad90e2f66a8c95425d3eddc91765abb6953bd3b48c0f')]:
        assert sha(ROOT/('paper/ht/pser/manuscript.'+ext))==expected_sha
    assert sha(ROOT/'paper/ht/pser/MATHEMATICAL_ERRATA.md')==frozen['governing_input/MATHEMATICS/MATHEMATICAL_ERRATA.md']['sha256']
    pins=json.loads((ROOT/'lean/lake-manifest.json').read_text())['packages']
    assert len(pins)==9 and {p['name']:p['rev'] for p in pins}==identity['dependency_pins']
    assert (ROOT/'lean/lean-toolchain').read_text().strip()=='leanprover/lean4:v4.34.1'
    if source_bundle:
        marker=read('HT22_SOURCE_BUNDLE.json')
        assert marker['source_identity_sha256']==sha(ROOT/'provenance/ht22/SOURCE_IDENTITY.json')
        actual={p.relative_to(ROOT).as_posix() for p in (ROOT/'lean').rglob('*.lean') if '.lake' not in p.parts}
        assert actual=={p for p in identity['files'] if p.startswith('lean/') and p.endswith('.lean')}
    if not source_bundle:
        publication=read('provenance/ht22/PUBLICATION_ALLOWLIST.json')
        edits=publication['files']
        assert set(edits)==set(read('provenance/ht22/OVERLAY_PLAN.json')['navigation_ci_allowlist'])
        assert all(not p.startswith(('lean/','provenance/lt22/','verification/lt22/','scripts/')) for p in edits)
        changed=[]
        for rel,item in baseline['files'].items():
            p=ROOT/rel;data=p.read_bytes()
            wanted=edits[rel]['new_sha256'] if rel in edits else item['sha256']
            assert not p.is_symlink() and sha(p)==wanted,('Unexpected old-file edit',rel)
            if rel in edits:
                old=ROOT/'provenance/ht22/historical-navigation'/rel
                assert sha(old)==item['sha256']==edits[rel]['old_sha256']
                changed.append(rel)
            else:
                assert hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==item['git_blob'],rel
        for rel in publication['workflow_body_sha256']:
            body='permissions:'+(ROOT/rel).read_text().split('\npermissions:',1)[1]
            assert hashlib.sha256(body.encode()).hexdigest()==publication['workflow_body_sha256'][rel],('Historical job logic edited',rel)
            text=(ROOT/rel).read_text()
            for part in [text.split('  pull_request:',1)[1].split('  push:',1)[0],text.split('  push:',1)[1].split('  workflow_dispatch:',1)[0]]:
                paths=re.findall(r"^      - '([^']+)'$",part,re.M)
                def matches(p):
                    yes=False
                    for pattern in paths:
                        if fnmatch.fnmatchcase(p,pattern.lstrip('!')):yes=not pattern.startswith('!')
                    return yes
                assert all(not matches(p) for p in identity['frozen_additions'])
                for p in ['lean/lake-manifest.json','lean/lean-toolchain','lean/lakefile.toml','lean/IsingBulk/HT/Final/PublishedPhysicalTheorem.lean','lean/IsingBulk/Final/UnconditionalNaturalBoundary.lean']:
                    assert matches(p),('Lost original/shared CI route',rel,p)
        actual_lean={p.relative_to(ROOT).as_posix() for p in (ROOT/'lean').rglob('*.lean') if '.lake' not in p.parts}
        wanted_lean={p for p in baseline['files'] if p.startswith('lean/') and p.endswith('.lean')}|{p for p in identity['frozen_additions'] if p.endswith('.lean')}
        assert actual_lean==wanted_lean,('Unmanifested/missing project Lean source',sorted(actual_lean^wanted_lean))
    result=dict(status='PASS',frozen_manifest_sha256=sha(ROOT/'provenance/ht22/FROZEN_SOURCE_MANIFEST.json'),frozen_ht22_modules=378,frozen_additions=len(identity['frozen_additions']),source_closure=len(identity['local_modules']),protected_files=3575 if not source_bundle else None,dependency_pins=identity['dependency_pins'],source_bundle=source_bundle)
    print(json.dumps(result,indent=2));return identity
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--source-bundle',action='store_true');a=p.parse_args();verify(a.source_bundle)
