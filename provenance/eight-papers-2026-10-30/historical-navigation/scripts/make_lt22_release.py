#!/usr/bin/env python3
"""Build compact frozen source assets and path-free public acceptance receipts."""
import argparse,hashlib,json,pathlib,shutil,zipfile
ROOT=pathlib.Path(__file__).resolve().parents[1]
TAG='lt22-preferred22-v1.0.0'
sha=lambda b:hashlib.sha256(b).hexdigest()

def main():
    p=argparse.ArgumentParser();p.add_argument('--output',required=True);p.add_argument('--commit',required=True);p.add_argument('--run-url',required=True);p.add_argument('--evidence',required=True);a=p.parse_args()
    out=pathlib.Path(a.output);out.mkdir(parents=True,exist_ok=False)
    evidence=pathlib.Path(a.evidence)
    accepted=json.loads((evidence/'SUMMARY.json').read_text())
    assert accepted['status']=='PASS' and accepted['official_fresh_kernel_exit_code']==0 and accepted['protected_files_unchanged'] is True
    identity=json.loads((ROOT/'provenance/lt22/SOURCE_IDENTITY.json').read_text())
    files={rel:(ROOT/rel).read_bytes() for rel in identity['files']}
    for rel in ['LICENSE','LICENSE-DOCUMENTATION.md','AUTHORSHIP.md','provenance/lt22/SOURCE_IDENTITY.json','provenance/lt22/AUDITED_GRAPH.json','provenance/lt22/PRIOR_ACCEPTANCE.json','verification/lt22/RootWalker.lean','verification/lt22/RootProbe.lean','scripts/verify_lt22_publication.py','scripts/run_lt22_acceptance.py','low-temperature/lt22/CITATION.cff']:
        files[rel]=(ROOT/rel).read_bytes()
    marker=dict(tag=TAG,commit=a.commit,source_identity_sha256=sha((ROOT/'provenance/lt22/SOURCE_IDENTITY.json').read_bytes()),scope='Exact frozen 486-module closure, configurations and manuscript; no project objects or dependency cache. Whole-repository preservation is certified by the linked release run.')
    files['LT22_SOURCE_BUNDLE.json']=(json.dumps(marker,indent=2)+'\n').encode()
    files['REPRODUCE.md']=b'''# LT22 Preferred22 source-only reproduction

Install the exact official Linux Lean 4.34.1 runtime and add its bin directory to PATH.
From this extracted directory:

    python3 scripts/verify_lt22_publication.py --source-bundle
    cd lean
    lake -f lakefile.toml exe cache get
    cd ..
    python3 -u scripts/run_lt22_acceptance.py --source-bundle --output /absolute/new/lt22-evidence

The runner rebuilds all 486 local modules from zero project objects, checks the exact
terminal type, allowed axioms and audited dependency graph, then runs official
leanchecker --fresh --verbose IsingBulk.Preferred22. It verifies source hashes again.
Only pinned third-party artifacts may be cached. Do not run lake update.

This compact bundle reproduces the frozen proof closure. The release's linked
combined-repository run separately certifies all protected original LT/HT/ANISO/JOINT
files and manuscript editions. No old Pro archive is needed.
'''
    files['INTERNAL_SHA256SUMS.txt']=''.join(sha(data)+'  '+rel+'\n' for rel,data in sorted(files.items())).encode()
    zp=out/'LT22_Preferred22_SOURCE_ONLY.zip'
    with zipfile.ZipFile(zp,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
        for rel,data in sorted(files.items()):
            zi=zipfile.ZipInfo(rel,date_time=(2026,10,27,0,0,0));zi.compress_type=zipfile.ZIP_DEFLATED;zi.external_attr=0o100644<<16;z.writestr(zi,data)
    for ext in ('pdf','tex'):shutil.copyfile(ROOT/f'paper/lt/pser/manuscript.{ext}',out/f'LT22_Preferred22_22page.{ext}')
    closure=json.loads((evidence/'CLOSURE.json').read_text())
    receipt=dict(tag=TAG,merged_main_sha=a.commit,acceptance_run_url=a.run_url,acceptance_job='preferred22',status='PASS',scope='combined-repository acceptance',source_identity=marker['source_identity_sha256'],clean_build=accepted['clean_build'],closure=closure,official_fresh_kernel_exit_code=0,protected_files_unchanged=True,prior_audit=json.loads((ROOT/'provenance/lt22/PRIOR_ACCEPTANCE.json').read_text()),assets={f.name:dict(bytes=f.stat().st_size,sha256=sha(f.read_bytes())) for f in sorted(out.iterdir())})
    (out/'LT22_PUBLICATION_RECEIPT.json').write_text(json.dumps(receipt,indent=2)+'\n')
    (out/'SHA256SUMS.txt').write_text(''.join(sha(f.read_bytes())+'  '+f.name+'\n' for f in sorted(out.iterdir()) if f.name!='SHA256SUMS.txt'))
    (out/'RELEASE_NOTES.md').write_text(f'''The frozen 22-page LT22 PSER proof and its independent Preferred22 route are published at `{a.commit}`.

The exact terminal declaration is `IsingBulk.Preferred22.preferred_full_target : IsingBulk.Preferred22.PreferredFullTarget`, with zero root premises. Precisely typed Yang and Palmer–Tracy real-temperature inputs occur only as antecedents within physical identification. The scope includes both pure phases, every lattice site including the origin, all positive even orders and the full connected infinite sum, every unit-circle point and physical inverse-temperature sheets.

Acceptance: [actual merged-main run]({a.run_url}), job `preferred22`: 486 distinct source-built modules, zero local object replays; exact audited stored dependency graph, allowed axioms only (`propext`, `Classical.choice`, `Quot.sound`); official fresh kernel replay exit 0. All protected original LT/HT/ANISO/JOINT sources, original/Reader manuscripts, historical identity records and dependency pins are preserved. The immutable October 25 EXHAUSTED audit is reused, without a new rescue or adversarial audit.

[Paper](https://github.com/LeoLam233/ising-bulk-natural-boundary/blob/{TAG}/paper/lt/pser/manuscript.pdf) · [TeX](https://github.com/LeoLam233/ising-bulk-natural-boundary/blob/{TAG}/paper/lt/pser/manuscript.tex) · [Theorem](https://github.com/LeoLam233/ising-bulk-natural-boundary/blob/{TAG}/lean/IsingBulk/Preferred22/FullTheorem.lean) · [Scope](https://github.com/LeoLam233/ising-bulk-natural-boundary/blob/{TAG}/docs/lt22/PROOF_MAP.md).

Assets include exact PDF/TeX, a compact source-only reproduction bundle, SHA-256 sums and a public receipt. Raw commands/streams and machine-readable evidence are downloadable from the linked Actions run. Dependency caches, local complete archives and credentials are excluded. Internal audit and formal acceptance do not claim human peer review or novelty clearance. HT22, ANISO F002 and JOINT F001 are separate tasks.
''')
    # Include the release notes in the checksums after their final bytes are written.
    (out/'SHA256SUMS.txt').write_text(''.join(sha(f.read_bytes())+'  '+f.name+'\n' for f in sorted(out.iterdir()) if f.name!='SHA256SUMS.txt'))
    print(json.dumps(receipt['assets'],indent=2))

if __name__=='__main__':main()
