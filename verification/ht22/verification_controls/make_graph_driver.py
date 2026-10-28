#!/usr/bin/env python3
"""Generate (never execute) a heavy RootWalker driver from exact protected code."""
import argparse,hashlib,json,pathlib,re,subprocess
HERE=pathlib.Path(__file__).resolve().parent
ROOT=HERE.parent
COMMIT='465375f2b6cc0952adaca87eddc859a40f577748'
def sha(data):return hashlib.sha256(data).hexdigest()
def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--case',choices=['final','bypass'],required=True)
    p.add_argument('--module',help='Actual final root module, e.g. IsingBulkHT22')
    p.add_argument('--root',default='IsingBulk.HT22.ht22_full_target')
    p.add_argument('--output',type=pathlib.Path,required=True)
    p.add_argument('--graph-base',type=pathlib.Path,required=True)
    p.add_argument('--protected-baseline',type=pathlib.Path,
                   help='Pinned PROTECTED_BASELINE.json for a snapshot without .git')
    a=p.parse_args()
    for n in [a.root]+([a.module] if a.module else []):
        if not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)*',n):p.error('invalid Lean name')
    if a.case=='final' and not a.module:p.error('final requires the actual --module')
    output=a.output.resolve();output.relative_to(HERE)
    base=a.graph_base.resolve();base.relative_to(HERE)
    scanner=ROOT/'repository/verification/lt22/RootWalker.lean'
    scanner_bytes=scanner.read_bytes()
    baseline=a.protected_baseline or (ROOT/'PROTECTED_BASELINE.json')
    blob=hashlib.sha1(b'blob '+str(len(scanner_bytes)).encode()+b'\0'+scanner_bytes).hexdigest()
    baseline_sha=None
    if baseline.is_file():
        baseline_bytes=baseline.read_bytes();baseline_sha=sha(baseline_bytes)
        pinned=json.loads(baseline_bytes)
        expected=pinned['files']['verification/lt22/RootWalker.lean']
        if pinned.get('commit')!=COMMIT or expected.get('sha256')!=sha(scanner_bytes) or expected.get('git_blob')!=blob:
            raise SystemExit('protected RootWalker baseline identity mismatch')
    else:
        if a.protected_baseline:raise SystemExit('explicit protected baseline does not exist')
        expected=subprocess.check_output(['git','show',COMMIT+':verification/lt22/RootWalker.lean'],cwd=ROOT/'repository')
        if scanner_bytes!=expected:raise SystemExit('protected RootWalker source identity mismatch')
    source=scanner_bytes.decode()
    if not source.startswith('import Lean\n'):raise SystemExit('unexpected scanner import header')
    source=source.removeprefix('import Lean\n')
    imports=['import Lean']; body='';fixture_sha=None
    if a.case=='final':imports+=['import '+a.module];root=a.root
    else:
        fixture=(HERE/'fixtures/OldRouteBypass.lean').read_bytes();fixture_sha=sha(fixture)
        lines=fixture.decode().splitlines(keepends=True)
        while lines and lines[0].startswith('import '):imports.append(lines.pop(0).strip())
        body=''.join(lines);root='AuditSentinel.oldRouteBypass'
    options={'maxRecDepth':100000,'maxHeartbeats':0,'pp.all':True,
             'pp.universes':True,'pp.proofs':True,'pp.explicit':True}
    option_source='\n'.join('set_option '+name+' '+str(value).lower()
                            for name,value in options.items())
    driver='\n'.join(dict.fromkeys(imports))+'\n'+option_source+'\n'+body+'\n'+source+'\n'
    driver+='audit_graph '+root+' to '+json.dumps(str(base))+'\n'
    output.parent.mkdir(parents=True,exist_ok=True);base.parent.mkdir(parents=True,exist_ok=True)
    output.write_text(driver)
    receipt=dict(case=a.case,root=root,scanner_path=str(scanner),scanner_sha256=sha(scanner_bytes),
                 scanner_git_blob=blob,protected_baseline_sha256=baseline_sha,
                 protected_repository_commit=COMMIT,fixture_sha256=fixture_sha,
                 driver_options=options,
                 output=str(output),driver_sha256=sha(output.read_bytes()),graph_base=str(base),executed=False)
    output.with_suffix('.driver.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
