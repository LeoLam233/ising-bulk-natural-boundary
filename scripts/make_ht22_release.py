#!/usr/bin/env python3
"""Make deterministic source-only assets; publish once after exact-main acceptance."""
import argparse,hashlib,json,pathlib,shutil,subprocess,sys,tempfile,urllib.request,zipfile
from verify_ht22_publication import ROOT,verify,sha,read
TAG='ht22-pser-f001-v1.0.0'
REPO='LeoLam233/ising-bulk-natural-boundary'
def digest(b):return hashlib.sha256(b).hexdigest()
def dump(p,v):p.write_text(json.dumps(v,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
def gh(*args):return subprocess.check_output(['gh',*args],text=True).strip()
def api(path):return json.loads(gh('api','repos/'+REPO+'/'+path))
def prepare(out,commit,run_url,evidence):
    identity=verify();accepted=json.loads((evidence/'SUMMARY.json').read_text());closure=json.loads((evidence/'ENHANCED_CLOSURE.json').read_text())
    assert accepted['status']=='PASS' and accepted['official_fresh_kernel_exit_code']==0 and accepted['protected_files_unchanged'] and accepted['field_count']==14
    assert accepted['github_sha']==commit and accepted['github_run_id']==run_url.rsplit('/',1)[-1]
    coverage=json.loads((evidence/'STRICT_COMPILER_COVERAGE.json').read_text())
    assert coverage['unique_source_compilations']==len(identity['local_modules']) and not coverage['missing']
    out.mkdir(parents=True,exist_ok=False)
    files={rel:(ROOT/rel).read_bytes() for rel in identity['files']}
    for rel in ['provenance/ht22/SOURCE_IDENTITY.json','provenance/ht22/PROTECTED_BASELINE.json','provenance/ht22/FROZEN_SOURCE_MANIFEST.json']:
        files[rel]=(ROOT/rel).read_bytes()
    marker=dict(tag=TAG,merged_main_sha=commit,source_identity_sha256=sha(ROOT/'provenance/ht22/SOURCE_IDENTITY.json'),original_source_zip_sha256='0e80db908bcb44298f3af03b19e322876e26c3b7028a1a3bcb91f272732437bd',scope='Exact frozen HT22 imported closure and complete additive coverage, pinned configs, manuscript and verification tooling. Dependencies are fetched at the unchanged nine locked revisions; no compiled objects or caches.')
    files['HT22_SOURCE_BUNDLE.json']=(json.dumps(marker,indent=2)+'\n').encode()
    files['REPRODUCE.md']=b'''# HT22 PSER F001 source-only reproduction

Use Ubuntu 24.04 / Python 3.12 and the official Lean 4.34.1 Linux runtime.
Download https://github.com/leanprover/lean4/releases/download/v4.34.1/lean-4.34.1-linux.tar.zst
and check SHA-256 47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4.
Extract it and add its bin directory to PATH. From this fresh source extraction:

    python3 scripts/verify_ht22_publication.py --source-bundle
    cd lean
    lake -f lakefile.ht22.toml exe cache get
    cd ..
    python3 -u scripts/run_ht22_acceptance.py --source-bundle --output /absolute/new/ht22-evidence

Never run lake update. Only official pinned third-party cache is fetched.
The runner independently copies the source and pinned dependencies, starts with
zero project objects, builds IsingBulkHT22, AuditHT22 and all 378 HT22 modules
with -j1 -DwarningAsError=true, reconstructs all fourteen stored field proofs,
checks complete enhanced type/value/structural support and real proof routes,
and separately runs official leanchecker --fresh --verbose IsingBulkHT22.
The kernel-valid old endpoint bypass must be rejected by route policy.

This bundle reproduces the entire frozen HT22 closure and its controls. Historical
whole-repository preservation is independently certified by the linked merged-main
CI run. Source-only mode reports that distinction explicitly. No private archive
or local path is needed. See docs/ht22/ for exact physical scope and correspondence.
'''
    files['INTERNAL_SHA256SUMS.txt']=''.join(digest(b)+'  '+rel+'\n' for rel,b in sorted(files.items())).encode()
    zp=out/'HT22_PSER_F001_SOURCE_ONLY.zip'
    with zipfile.ZipFile(zp,'w',zipfile.ZIP_DEFLATED,compresslevel=9) as z:
        for rel,b in sorted(files.items()):
            assert '.git' not in pathlib.PurePosixPath(rel).parts and '.lake' not in pathlib.PurePosixPath(rel).parts and '.olean' not in rel
            zi=zipfile.ZipInfo(rel,(2026,10,28,0,0,0));zi.compress_type=zipfile.ZIP_DEFLATED;zi.external_attr=0o100644<<16;z.writestr(zi,b)
    with tempfile.TemporaryDirectory(prefix='ht22-release-extract-') as tmp:
        with zipfile.ZipFile(zp) as z:
            assert z.testzip() is None
            for rel,b in files.items():assert z.read(rel)==b,rel
            z.extractall(tmp)
        subprocess.run([sys.executable,str(pathlib.Path(tmp)/'scripts/verify_ht22_publication.py'),'--source-bundle'],check=True)
    for ext in ['pdf','tex']:shutil.copyfile(ROOT/('paper/ht/pser/manuscript.'+ext),out/('HT22_PSER_F001_22page.'+ext))
    notes=f'''# HT22 — independent 22-page high-temperature PSER proof

Immutable tag `{TAG}` identifies the normally merged main commit `{commit}`.
[Successful merged-main acceptance]({run_url}), job `ht22`, governs this release.

The exact parameter-free theorem is `IsingBulk.HT22.ht22_full_target : IsingBulk.HT22.HT22FullTarget`, with fourteen actual proved fields: full-disk analyticity, every-point unit-circle obstruction, beta-inclusive susceptibility, equality to the old HT germs, the conditional full-site physical interpretation, beta coordinate, joint lattice/odd-particle summability, one-particle identity, complete differentiated absolute tail, exact FIRST coefficient, full prime limit, angular jets and sharp covariance jets. The independent route does not consume the old HT finished boundary, FIRST, noncancellation or differentiated-tail endpoints.

Physical interpretation is conditional on precisely `PhysicalScope.PublishedRealHTSpinFormFactors corr` (onsite spin-square and sitewise real odd form factors). Lean does not construct Gibbs states or derive those real physical identities unconditionally.

This commit passed a source-clean strict build of all {coverage['unique_source_compilations']} local source modules needed for complete additive coverage and the negative fixture, including all 378 HT22 submodules, strict AuditHT22, separate official `lake -f lakefile.ht22.toml env leanchecker --fresh --verbose IsingBulkHT22` (exit 0), all fourteen stored field types/proofs, enhanced full type/stored-value/mutual-inductive/constructor/reverse-recursor/quotient closure, and positive/negative route controls. Only `propext`, `Classical.choice`, `Quot.sound` occur. Required MAIN mechanisms occur on stored-value/structural paths excluding type edges. The old-endpoint bypass compiles and is policy-rejected. Exact original mathematical sources, manuscripts and nine pins are preserved; the explicit navigation/CI allowlist is separately hashed and diffed. Historical verification algorithms are unchanged.

The supplied Dot internal audit receipts and completed external Codex C001 and persistent-Pro AI adversarial audit identities report EXHAUSTED on the exact frozen source. They are provenance, distinct from this run's kernel checks. No new human peer review or novelty clearance is claimed. Large private archives remain at their existing custody locations.

[Frozen PDF](https://github.com/{REPO}/blob/{TAG}/paper/ht/pser/manuscript.pdf) · [TeX](https://github.com/{REPO}/blob/{TAG}/paper/ht/pser/manuscript.tex) · [Clarifications](https://github.com/{REPO}/blob/{TAG}/paper/ht/pser/MATHEMATICAL_ERRATA.md) · [Theorem](https://github.com/{REPO}/blob/{TAG}/lean/IsingBulk/HT22/Final/Target.lean) · [Scope](https://github.com/{REPO}/blob/{TAG}/docs/ht22/PHYSICAL_INPUTS.md).

Assets contain exact frozen PDF/TeX, a deterministic source-only reproduction ZIP, receipt, these notes and SHA-256 sums. Raw commands, logs, source/object hashes and complete graph/field records are retained as Actions artifacts in the linked run. Original/Reader HT, LT22 and all previous releases remain separate editions.
'''
    (out/'RELEASE_NOTES.md').write_text(notes,encoding='utf-8')
    receipt=dict(schema='HT22-publication-receipt-v1',status='PASS',tag=TAG,merged_main_sha=commit,acceptance_run_url=run_url,acceptance_job='ht22',theorem='IsingBulk.HT22.ht22_full_target : IsingBulk.HT22.HT22FullTarget',root_premises=0,field_count=14,original_source_zip_sha256=marker['original_source_zip_sha256'],original_source_manifest_sha256='a0c4ddb4725a86382ee8f57e1e81b25cf60b8a2e1469d165c9efa395a65d227f',source_identity_sha256=marker['source_identity_sha256'],strict_source_compilations=coverage['unique_source_compilations'],complete_additive_modules=378,official_fresh_kernel_exit_code=0,enhanced_closure=closure,protected_original_files=3575,protected_mathematical_changes=0,publication_allowlist_sha256=sha(ROOT/'provenance/ht22/PUBLICATION_ALLOWLIST.json'),prior_audits=read('provenance/ht22/PRIOR_AUDITS.json'),source_bundle_fresh_extraction_verified=True,assets={p.name:dict(bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(out.iterdir())})
    dump(out/'HT22_PUBLICATION_RECEIPT.json',receipt)
    (out/'SHA256SUMS.txt').write_text(''.join(sha(p)+'  '+p.name+'\n' for p in sorted(out.iterdir())),encoding='utf-8')
def publish(out,commit,run_url):
    assert api('git/ref/heads/main')['object']['sha']==commit,'main moved'
    jobs=api('actions/runs/'+run_url.rsplit('/',1)[-1]+'/jobs')['jobs']
    assert any(j['name']=='ht22' and j['conclusion']=='success' and j['head_sha']==commit for j in jobs),'No successful exact-main acceptance'
    release_json=subprocess.run(['gh','api','repos/'+REPO+'/releases/tags/'+TAG],text=True,capture_output=True)
    if release_json.returncode==0:
        release=json.loads(release_json.stdout)
    else:
        tag=subprocess.run(['gh','api','repos/'+REPO+'/git/ref/tags/'+TAG],text=True,capture_output=True)
        if tag.returncode==0:assert json.loads(tag.stdout)['object']['sha']==commit,'Existing immutable tag mismatch'
        else:gh('api','--method','POST','repos/'+REPO+'/git/refs','-f','ref=refs/tags/'+TAG,'-f','sha='+commit)
        asset_files=[p for p in sorted(out.iterdir()) if p.is_file()]
        gh('release','create',TAG,'--repo',REPO,'--verify-tag','--draft','--title','HT22 — independent 22-page high-temperature PSER proof','--notes-file',str(out/'RELEASE_NOTES.md'),*[str(p) for p in asset_files])
        release=api('releases/tags/'+TAG)
    target=api('git/ref/tags/'+TAG)['object']
    if target['type']=='tag':target=api('git/tags/'+target['sha'])['object']
    assert target['sha']==commit
    expected={p.name:p for p in out.iterdir() if p.is_file()}
    assert {a['name'] for a in release['assets']}==set(expected),'Release asset inventory differs'
    if release['draft']:
        # Verify every draft asset before publishing locks its bytes and tag.
        with tempfile.TemporaryDirectory(prefix='ht22-draft-readback-') as tmp:
            gh('release','download',TAG,'--repo',REPO,'--dir',tmp)
            for name,p in expected.items():assert sha(pathlib.Path(tmp)/name)==sha(p),name
        gh('release','edit',TAG,'--repo',REPO,'--draft=false')
        release=api('releases/tags/'+TAG)
    assert release.get('immutable') is True,'GitHub release/tag immutability is not enforced'
    checks={}
    for asset in release['assets']:
        p=expected[asset['name']]
        raw=urllib.request.urlopen(urllib.request.Request(asset['browser_download_url'],headers={'User-Agent':'HT22-publication-readback'})).read()
        assert len(raw)==p.stat().st_size and digest(raw)==sha(p),asset['name']
        checks[asset['name']]=dict(url=asset['browser_download_url'],bytes=len(raw),sha256=digest(raw))
    dump(out/'RELEASE_READBACK.json',dict(status='VERIFIED',release_url=release['html_url'],merged_main_sha=commit,tag_target=target['sha'],github_immutable=True,assets=checks))
def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=pathlib.Path,required=True);p.add_argument('--commit',required=True);p.add_argument('--run-url',required=True);p.add_argument('--evidence',type=pathlib.Path,required=True);p.add_argument('--publish',action='store_true');a=p.parse_args()
    prepare(a.output,a.commit,a.run_url,a.evidence)
    if a.publish:publish(a.output,a.commit,a.run_url)
if __name__=='__main__':main()
