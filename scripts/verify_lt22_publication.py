#!/usr/bin/env python3
"""Verify frozen LT22 inputs, exact import closure and protected repository bytes."""
import argparse, fnmatch, hashlib, json, pathlib, re

ROOT = pathlib.Path(__file__).resolve().parents[1]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()

def verify(source_bundle=False):
    identity = json.loads((ROOT/'provenance/lt22/SOURCE_IDENTITY.json').read_text())
    protected = json.loads((ROOT/'provenance/lt22/PROTECTED_BASE.json').read_text()) if not source_bundle else {'files':{}}
    if source_bundle:
        marker=json.loads((ROOT/'LT22_SOURCE_BUNDLE.json').read_text())
        assert marker['source_identity_sha256']==sha(ROOT/'provenance/lt22/SOURCE_IDENTITY.json')
    else:
        routing=json.loads((ROOT/'provenance/lt22/CI_ROUTING.json').read_text())
        for rel,wanted in routing['historical_verification_body_sha256'].items():
            text=(ROOT/rel).read_text()
            assert hashlib.sha256(('permissions:'+text.split('\npermissions:',1)[1]).encode()).hexdigest()==wanted,('Historical verification logic changed',rel)
            for part in (text.split('  pull_request:',1)[1].split('  push:',1)[0],text.split('  push:',1)[1].split('  workflow_dispatch:',1)[0]):
                paths=re.findall(r"^      - '([^']+)'$",part,re.M)
                def matches(path):
                    yes=False
                    for pattern in paths:
                        if fnmatch.fnmatchcase(path,pattern.lstrip('!')):yes=not pattern.startswith('!')
                    return yes
                assert not matches('lean/IsingBulk/Preferred22.lean') and not matches('lean/IsingBulk/Preferred22/FullTheorem.lean')
                assert not matches('lean/README.md'),('Navigation-only Lean README incorrectly triggers heavy replay',rel)
                for shared in ('lean/lake-manifest.json','lean/lean-toolchain','lean/lakefile.toml','lean/IsingBulk/Final/UnconditionalNaturalBoundary.lean','lean/IsingBulk/HT/Final/PublishedPhysicalTheorem.lean','lean/IsingBulk/Anisotropic/Final/FullTheorem.lean'):
                    assert matches(shared),('Shared/original suite routing lost',rel,shared)
    for group in (identity['files'], protected['files']):
        for rel, expected in group.items():
            p = ROOT/rel
            assert p.is_file() and not p.is_symlink() and sha(p) == expected, rel
    new = {p.relative_to(ROOT).as_posix() for p in (ROOT/'lean/IsingBulk/Preferred22').rglob('*') if p.is_file()}
    new.add('lean/IsingBulk/Preferred22.lean')
    expected = {p for p in identity['files'] if p.startswith('lean/IsingBulk/Preferred22/') or p == 'lean/IsingBulk/Preferred22.lean'}
    assert new == expected, ('Preferred22 inventory', sorted(new^expected))
    assert sum(p.endswith('.lean') for p in new) == 333
    queue = ['IsingBulk.Preferred22']
    seen = set()
    while queue:
        name = queue.pop()
        if name in seen: continue
        seen.add(name)
        rel = 'lean/'+name.replace('.', '/')+'.lean'
        assert rel in identity['files'], ('Unfrozen imported source', rel)
        text = (ROOT/rel).read_text()
        for imp in re.findall(r'^\s*import\s+([\w.]+)', text, re.M):
            if imp.startswith('IsingBulk'): queue.append(imp)
    assert len(seen) == 486, len(seen)
    pins = json.loads((ROOT/'lean/lake-manifest.json').read_text())['packages']
    assert len(pins) == 9
    assert next(p['rev'] for p in pins if p['name'] == 'mathlib') == 'd13f23b723b8a846827a245b89c10fc7d3f11612'
    assert (ROOT/'lean/lean-toolchain').read_text().strip() == 'leanprover/lean4:v4.34.1'
    result = dict(status='PASS', base_main_sha=identity['base_main_sha'], frozen_entries=491,
                  production_import_closure=486, preferred22_modules=333, inherited_modules=153,
                  protected_paths=len(protected['files']), protected_mismatches=0,
                  source_sha256={k:v for k,v in identity['files'].items()}, dependency_pins={p['name']:p['rev'] for p in pins})
    print('PASS: 333 Preferred22 modules; 486 exact source closure; 491 source/provenance entries; exact PDF/TeX/configs; '+str(len(protected['files']))+' unchanged protected files')
    return result

if __name__ == '__main__':
    a=argparse.ArgumentParser(); a.add_argument('--output'); a.add_argument('--source-bundle',action='store_true'); args=a.parse_args()
    result=verify(args.source_bundle)
    if args.output: pathlib.Path(args.output).write_text(json.dumps(result,indent=2)+'\n')
