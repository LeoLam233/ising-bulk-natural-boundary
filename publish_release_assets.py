"""Assemble hash-bound release evidence; publish only the verified merged tree."""
import base64
import hashlib
import io
import json
import mimetypes
import os
from pathlib import Path
import subprocess
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
import zipfile

M=json.loads(Path('release-assets-manifest.json').read_text())
REPO=M['repository']
API='https://api.github.com/repos/'+REPO
TOKEN=os.environ['GH_TOKEN']
OUT=Path(os.environ['RUNNER_TEMP'])/'high-temperature-release-assets'
OUT.mkdir(exist_ok=True)

class SafeRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self,req,fp,code,msg,headers,newurl):
        result=super().redirect_request(req,fp,code,msg,headers,newurl)
        if result is not None and urllib.parse.urlparse(newurl).netloc != urllib.parse.urlparse(req.full_url).netloc:
            result.remove_header('Authorization')
        return result

OPENER=urllib.request.build_opener(SafeRedirect)

def request(method,path,payload=None,binary=None,accept='application/vnd.github+json',content_type=None):
    url=path if path.startswith('https://') else API+path
    assert urllib.parse.urlparse(url).netloc in ['api.github.com','uploads.github.com']
    headers={'Authorization':'Bearer '+TOKEN,'Accept':accept,'X-GitHub-Api-Version':'2022-11-28','User-Agent':'ising-ht-1747-publication'}
    if payload is not None:
        binary=json.dumps(payload).encode();headers['Content-Type']='application/json'
    if content_type:headers['Content-Type']=content_type
    for attempt in range(5):
        try:
            with OPENER.open(urllib.request.Request(url,data=binary,headers=headers,method=method),timeout=180) as response:
                return response.read()
        except urllib.error.HTTPError as error:
            if error.code in [429,500,502,503,504] and attempt<4:
                time.sleep(min(5*(attempt+1),30));continue
            raise RuntimeError(f'GitHub {method} {path}: HTTP {error.code}: '+error.read(4000).decode(errors='replace')) from error

def api(method,path,payload=None):
    data=request(method,path,payload)
    return json.loads(data) if data else None

def sha(data):return hashlib.sha256(data).hexdigest()

def json_file(name,value):
    path=OUT/name
    path.write_bytes((json.dumps(value,indent=2,sort_keys=True,ensure_ascii=False)+'\n').encode())
    return path

subprocess.run([sys.executable,'scripts/verify_unified_publication.py'],check=True)
for asset in M['assets']:
    data=bytearray()
    for chunk in asset['chunks']:
        blob=api('GET','/git/blobs/'+chunk['sha'])
        block=base64.b64decode(blob['content'])
        assert len(block)==chunk['bytes'] and sha(block)==chunk['sha256'],asset['name']
        data.extend(block)
    assert len(data)==asset['bytes'] and sha(data)==asset['sha256'],asset['name']
    (OUT/asset['name']).write_bytes(data)
    print('ASSEMBLED',asset['name'],len(data),sha(data),flush=True)

releases=api('GET','/releases?per_page=100')
candidates=[r for r in releases if r['tag_name']==M['tag'] or (r['draft'] and r['name']==M['title'])]
assert len(candidates)<=1,'Ambiguous high-temperature release identity'
release=candidates[0] if candidates else api('POST','/releases',dict(tag_name=M['tag'],target_commitish=M['head_sha'],name=M['title'],draft=True,body='Publication preparation; verification and merge gates remain mandatory.'))
if M['phase']=='stage':assert release['draft'],'Staging cannot modify a published release'

if M['phase']=='publish':
    pull=api('GET','/pulls/4')
    assert pull['merged'] and pull['head']['sha']==M['head_sha']
    assert pull['merge_commit_sha']==M['merge_sha']
    main=api('GET','/git/ref/heads/main')['object']['sha']
    assert main==M['merge_sha'],'main moved away from the approved merge'
    commit=api('GET','/git/commits/'+main)
    assert commit['tree']['sha']==M['source_tree'],'Merged source tree differs from verified publication tree'
    for tag,expected in M['historical_tags'].items():
        actual=api('GET','/git/ref/tags/'+urllib.parse.quote(tag,safe=''))['object']['sha']
        assert actual==expected,'Historical tag changed: '+tag
    github_files={}
    for run_id in M['required_runs']:
        run=api('GET',f'/actions/runs/{run_id}')
        assert run['head_sha']==M['head_sha'] and run['status']=='completed' and run['conclusion']=='success',run_id
        summary={k:run[k] for k in ['id','name','head_sha','status','conclusion','html_url','run_attempt','created_at','updated_at']}
        github_files[f'runs/{run_id}/run.json']=(json.dumps(summary,indent=2)+'\n').encode()
        jobs=api('GET',f'/actions/runs/{run_id}/jobs?per_page=100')['jobs']
        assert jobs and all(j['conclusion']=='success' for j in jobs),run_id
        for job in jobs:
            github_files[f'runs/{run_id}/jobs/{job["id"]}.json']=(json.dumps(job,indent=2)+'\n').encode()
            github_files[f'runs/{run_id}/jobs/{job["id"]}.log']=request('GET',f'/actions/jobs/{job["id"]}/logs')
        artifacts=api('GET',f'/actions/runs/{run_id}/artifacts?per_page=100')['artifacts']
        assert artifacts,'Missing execution artifacts'
        for artifact in artifacts:
            archive=request('GET',f'/actions/artifacts/{artifact["id"]}/zip')
            with zipfile.ZipFile(io.BytesIO(archive)) as z:
                assert z.testzip() is None
                for member in z.infolist():
                    if member.is_dir():continue
                    assert '..' not in Path(member.filename).parts
                    github_files[f'artifacts/{artifact["name"]}/{member.filename}']=z.read(member)
    evidence=OUT/'HT_1747_GITHUB_ACCEPTANCE_RECORDS.zip'
    with zipfile.ZipFile(evidence,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
        for name,data in sorted(github_files.items()):
            info=zipfile.ZipInfo(name,date_time=(2026,10,21,0,0,0));info.compress_type=zipfile.ZIP_DEFLATED
            z.writestr(info,data)
    manifest=json.loads(Path('HT_1747_OVERLAY_MANIFEST.json').read_text())
    identity=dict(repository=REPO,tag=M['tag'],pull_request='https://github.com/'+REPO+'/pull/4',
        merged_commit=main,verified_head=M['head_sha'],source_tree=M['source_tree'],
        audited_project='HT_STANDALONE_20261020T1747Z',unchanged_baseline_files=len(manifest['baseline_files']),
        exact_overlay_files=len(manifest['overlay_files']),original_standalone_matching_files=1521,
        low_temperature_baseline_tree=manifest['lt_existing_git_tree'],historical_tag_refs=M['historical_tags'],
        lean='4.34.1',lean_compiler_commit='5045d0056413266e57c625dcd7c365b10e377c52',
        mathlib='d13f23b723b8a846827a245b89c10fc7d3f11612',
        publication_build=json.loads(Path('paper/ht/publication/BUILD.json').read_text()),
        editorial=json.loads(Path('paper/ht/publication/EDITORIAL.json').read_text()),
        required_github_runs=M['required_runs'],source_manifest_sha256=sha(Path('HT_1747_OVERLAY_MANIFEST.json').read_bytes()),
        assets={a['name']:dict(bytes=a['bytes'],sha256=a['sha256']) for a in M['assets']},
        source_files={**manifest['baseline_files'],**manifest['overlay_files']})
    json_file('HT_1747_SOURCE_IDENTITY.json',identity)
    sums=''.join(sha(p.read_bytes())+'  '+p.name+'\n' for p in sorted(OUT.iterdir()) if p.is_file())
    (OUT/'SHA256SUMS.txt').write_bytes(sums.encode())

assets_by_name={a['name']:a for a in api('GET',f'/releases/{release["id"]}/assets?per_page=100')}
uploaded=[]
for path in sorted(OUT.iterdir()):
    if not path.is_file():continue
    data=path.read_bytes();digest=sha(data)
    if path.name in assets_by_name:
        existing=assets_by_name[path.name]
        if existing.get('digest')!='sha256:'+digest:
            old=request('GET',f'/releases/assets/{existing["id"]}',accept='application/octet-stream')
            assert sha(old)==digest,'Existing release asset has different bytes: '+path.name
        uploaded.append(existing)
        print('EXACT_ASSET_ALREADY_PRESENT',path.name,digest,flush=True)
        continue
    url=f'https://uploads.github.com/repos/{REPO}/releases/{release["id"]}/assets?name='+urllib.parse.quote(path.name)
    result=json.loads(request('POST',url,binary=data,content_type=mimetypes.guess_type(path.name)[0] or 'application/octet-stream'))
    assert result['size']==len(data)
    assert result.get('digest') in [None,'sha256:'+digest]
    uploaded.append(result)
    print('UPLOADED',path.name,digest,result['browser_download_url'],flush=True)

if M['phase']=='publish':
    base='https://github.com/'+REPO
    release_url=base+'/releases/tag/'+M['tag']
    body=f'''This is the distinct **high-temperature-phase** result for the complete zero-field bulk magnetic susceptibility of the disordered infinite square-lattice Ising phase, including the **full infinite positive odd-particle form-factor sum**. Every point of the unit circle is a natural-boundary point of its disk germ.

The separate [low-temperature proof]({base}/tree/{M['tag']}/low-temperature) concerns the **connected ordered pure-phase susceptibility** and its complete infinite even-particle sum. Its original manuscripts, source files, tags, snapshots and release assets retain their historical identities.

**Merged commit:** `{M['merge_sha']}` ([PR #4]({base}/pull/4)).
**Verified publication tree:** `{M['source_tree']}`.
**Audited HT mathematical project:** `HT_STANDALONE_20261020T1747Z`.

All **1,079 baseline files** and **447 additive overlay files** match the archived SHA-256 manifest; all **1,521 original standalone project files** match byte for byte. Existing LT mathematical files are unchanged. No compiled Lean artifacts or large audit archives are added to the production source tree.

The publication manuscript is **HT-1.0, 17 October 2026; editorial publication edition 21 October 2026**. Human author: **Dehao Lin**, School of Physics, Sun Yat-sen University; ORCID [0009-0001-4551-8490](https://orcid.org/0009-0001-4551-8490); lindh9@mail2.sysu.edu.cn. Exactly three preamble metadata lines differ from the preserved frozen manuscript. The entire mathematical document body is byte-identical, and all 34 publication PDF pages were rendered and inspected.

The final Lean theorem [`publishedPhysicalSusceptibility_germ_natural_boundary`]({base}/blob/{M['tag']}/lean/IsingBulk/HT/Final/PublishedPhysicalTheorem.lean) assumes positive coupling and the precisely stated **published real-temperature full-bulk angular form-factor representation**. It constructs a disk-analytic realization agreeing with the physical susceptibility on every real `0 < s < 1`, with no local continuation through any unit-circle point. No FIRST, TAIL, summability, contour-equality, analyticity or natural-boundary premise is hidden in that physical input. The compiled audit rejects actual dependencies on the LT final natural-boundary theorem and its E1/E2/E3 physical interfaces.

Verification used **Lean 4.34.1**, compiler commit `5045d0056413266e57c625dcd7c365b10e377c52`, and all nine pinned dependencies, including Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. The HT full build began with zero project `.olean` files; only pinned dependency caches were reused. These required commands succeeded:

```sh
lake -f lakefile.toml build IsingBulk Audit
lake -f lakefile.ht.toml -R -H build IsingBulkHT AuditHT
lake -f lakefile.ht.toml env lean -j1 -DwarningAsError=true AuditHT.lean
lake -f lakefile.ht.toml env leanchecker --fresh --verbose IsingBulkHT
```

The local source-only verification and the final-tree GitHub checks have full execution records. GitHub additionally replayed the LT root freshly. See [HT acceptance]({base}/actions/runs/{M['required_runs'][0]}) and [combined HT/LT acceptance]({base}/actions/runs/{M['required_runs'][1]}). `HT_1747_GITHUB_ACCEPTANCE_RECORDS.zip` preserves job logs and artifacts; the separate local verification archive preserves raw stdout/stderr, exact commands, exit codes, runtimes, identities and source hashes. `HT_1747_SOURCE_IDENTITY.json` and `SHA256SUMS.txt` bind the source and attachments.

Independent AI evidence is preserved as separate release assets: [Pro/coordinated source audits]({release_url.replace('/tag/','/download/')}/HT_Lean_1747_1_Source_Audits.zip), [original execution logs]({release_url.replace('/tag/','/download/')}/HT_Lean_1747_2_Execution_Logs.zip), [original final-gate receipt]({release_url.replace('/tag/','/download/')}/HT_Lean_1747_3_Original_Receipt.zip), and the [independent Codex audit]({release_url.replace('/tag/','/download/')}/HT_LEAN_1747_AUDIT_20261021.zip). Their original `EXHAUSTED` verdicts retain their documented scope. AI audits are not independent human peer review.

Lean code is **MIT**. The author-created manuscript and documentation are **CC BY 4.0**, to the extent of the author's rights. Use the separate [high-temperature citation]({base}/blob/{M['tag']}/high-temperature/CITATION.cff) and [low-temperature citation]({base}/blob/{M['tag']}/low-temperature/CITATION.cff).
'''
    release=api('PATCH',f'/releases/{release["id"]}',dict(tag_name=M['tag'],target_commitish=M['merge_sha'],name=M['title'],body=body,draft=False,prerelease=False,make_latest='true'))
    assert not release['draft'] and release['tag_name']==M['tag'] and release['published_at']
    tag=api('GET','/git/ref/tags/'+urllib.parse.quote(M['tag'],safe=''))['object']
    target=tag['sha']
    if tag['type']=='tag':target=api('GET','/git/tags/'+target)['object']['sha']
    assert target==M['merge_sha'],'Published tag points to a different commit'
    uploaded=api('GET',f'/releases/{release["id"]}/assets?per_page=100')
    print('PUBLISHED_VERIFIED',release['html_url'],target,flush=True)

report=dict(phase=M['phase'],release_id=release['id'],release_url=release['html_url'],draft=release['draft'],
            tag=M['tag'],assets=[dict(name=a['name'],size=a['size'],url=a['browser_download_url'],digest=a.get('digest')) for a in uploaded])
Path(os.environ['RUNNER_TEMP'],'release-operation.json').write_bytes((json.dumps(report,indent=2)+'\n').encode())
print(json.dumps(report,indent=2),flush=True)
