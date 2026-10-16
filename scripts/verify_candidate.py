"""Check the current candidate, its final inventory and frozen historical bytes.

Requires a Git checkout. Hash/consistency checks are not mathematical certification.
"""
import argparse,csv,hashlib,json,pathlib,re,subprocess,sys,tarfile
ROOT=pathlib.Path(__file__).resolve().parents[1]
MANIFEST='release/next/MANIFEST.json'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(name):return json.loads((ROOT/name).read_text(encoding='utf-8'))

def identity(value):
    return hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':'),ensure_ascii=False).encode()).hexdigest()
def require(ok,message):
    if not ok:raise RuntimeError(message)
def tracked():
    data=subprocess.check_output(['git','-c','safe.directory=*','ls-files','-z'],cwd=ROOT)
    return sorted(set(data.decode().split('\0'))-{''})
def inventory():
    entries=[]
    for name in tracked():
        if name==MANIFEST:continue
        p=ROOT/name
        require(p.is_file() and not p.is_symlink(),'Missing/linked tracked file: '+name)
        require(p.resolve().is_relative_to(ROOT),'Escaping path: '+name)
        entries.append({'path':name,'bytes':p.stat().st_size,'sha256':sha(p)})
    return entries
def semantic():
    baseline=read('provenance/NEXT_BASELINE.json')
    for e in baseline['protected_files']:
        require(sha(ROOT/e['path'])==e['sha256'],'Protected historical asset changed: '+e['path'])
    hist=read('lean/history/v0.2.1/INDEX.json')
    for e in hist['files']:
        require(sha(ROOT/e['historical_copy'])==e['sha256'],'Historical copy changed: '+e['historical_copy'])
    for tag,expected in [('v0.1-rc4',baseline['frozen_manuscript_tag']),('v0.2.1',baseline['frozen_lean_tag'])]:
        actual=subprocess.check_output(['git','-c','safe.directory=*','rev-parse',tag+'^{}'],cwd=ROOT,text=True).strip()
        require(actual==expected,'Frozen tag moved: '+tag)
    old_notes=subprocess.check_output(['git','-c','safe.directory=*','show',baseline['baseline_commit']+':RELEASE_NOTES.md'],cwd=ROOT)
    require((ROOT/'RELEASE_NOTES.md').read_bytes().endswith(old_notes),'Historical release-note blocks changed')
    source=read('lean/SOURCE.json');build=read('paper/next/BUILD.json');qa=read('release/next/PDF_QA.json')
    paper=ROOT/'paper/next/manuscript.tex';data=paper.read_bytes()
    require((ROOT/'lean'/source['local_copy']).read_bytes()==data,'Candidate source snapshot differs')
    require(source['sha256']==build['source_sha256']==sha(paper),'Candidate source hash mismatch')
    blob=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
    require(blob==source['expected_git_blob']==source['computed_git_blob'],'Candidate manuscript blob mismatch')
    pinned=subprocess.check_output(['git','-c','safe.directory=*','rev-parse',
        source['repository_snapshot_commit']+':'+source['manuscript_path']],cwd=ROOT,text=True).strip()
    require(pinned==blob,'Source commit does not contain the current manuscript')
    require(build['pdf_sha256']==qa['pdf_sha256']==sha(ROOT/'paper/next/manuscript.pdf'),'PDF/QA hash mismatch')
    require(build['label_index_sha256']==sha(ROOT/'paper/next/LABEL_INDEX.json'),'Label index hash mismatch')
    old=read('paper/LABEL_INDEX.json');new=read('paper/next/LABEL_INDEX.json')
    labels={e['label']:e['number'] for e in new}
    require(len(new)==len(labels)==67,'Candidate label inventory mismatch')
    require(all(labels[e['label']]==e['number'] for e in old),'Existing mathematical numbering drifted')
    require(set(re.findall(r'\\label\{([^}]+)\}',data.decode()))==set(labels),'Source/index labels differ')
    require(labels['cor:smootharc']=='9.4' and labels['eq:amplitudeclosed']=='B.1','New statement numbering mismatch')
    require('Version 0.1-rc5' in data.decode(),'Candidate self-label mismatch')
    config=read('lean/TOOLCHAIN_FREEZE.json');contract=read('lean/tools/continuation/endpoint_contract.json')
    for e in config['files']:require(sha(ROOT/'lean'/e['path'])==e['sha256'],'Config pin mismatch: '+e['path'])
    require(contract['frozen_config_sha256']=={e['path']:e['sha256'] for e in config['files']},'Contract/config mismatch')
    require(contract['manuscript_git_blob']==blob,'Contract source blob mismatch')
    prod={p.relative_to(ROOT/'lean').as_posix() for p in (ROOT/'lean/IsingBulk').rglob('*.lean')}|{'IsingBulk.lean'}
    payload=read('lean/ci/payload.json');accepted=read('lean/ci/accepted_identity.json')
    inputs=payload['proof_inputs'];actual=dict(inputs);actual['files']={}
    require(prod=={p for p in inputs['files'] if p.endswith('.lean')},'Production payload inventory mismatch')
    for name,expected in inputs['files'].items():
        digest=sha(ROOT/'lean'/name);require(digest==expected,'Proof payload changed: '+name)
        actual['files'][name]=digest
    pid=identity(actual)
    require(pid==payload['PROOF_CRITICAL_PAYLOAD_ID']==accepted['PROOF_CRITICAL_PAYLOAD_ID'],'Proof identity mismatch')
    # Recompute current verification bytes, not just the equality of two pins.
    vp=['Audit.lean','CLAIM_LEDGER.tsv','CORRESPONDENCE.md','COVERAGE.md','GAP_MANIFEST.md',
        'CONTINUATION_SOURCE_CORRESPONDENCE.md','CONTINUATION_AUXILIARY_SCOPE.md',
        'tools/continuation/source_references.json']
    controls=ROOT/'lean/control_packet/continuation';generated={'results','logs','run_logs','__pycache__'}
    for p in controls.rglob('*'):
        if p.is_file() and not generated.intersection(p.relative_to(controls).parts) and p.suffix in {'.py','.lean','.json','.md','.toml','.sh','.ps1'}:
            vp.append(p.relative_to(ROOT/'lean').as_posix())
    verification={p:sha(ROOT/'lean'/p) for p in sorted(set(vp))}
    verification.update({'tool:'+p.name:sha(p) for p in (ROOT/'lean/tools/continuation').iterdir()
        if p.is_file() and p.suffix in {'.py','.json','.md','.lean'}})
    verification['endpoint_contract_content']=identity(contract)
    require(identity(verification)==accepted['VERIFICATION_INPUT_ID'],'Current verification bytes differ from the executed gate')
    with (ROOT/'lean/CLAIM_LEDGER.tsv').open(encoding='utf-8',newline='') as f:rows=list(csv.DictReader(f,delimiter='\t'))
    require(all(e['source_commit']==source['repository_snapshot_commit'] for e in rows),'Ledger source version drift')
    refs=read('lean/tools/continuation/source_references.json')['references']
    keys={(e['source_label'],x.strip()) for e in rows for x in e['lean_declaration'].split(';') if x.strip()}
    require(keys=={(e['source_label'],e['ledger_token']) for e in refs},'Ledger/map mismatch')
    require(len(contract['endpoints'])==18,'Endpoint contract count mismatch')
    for f in ['README.md','README.zh.md','CLAIMS.md','LIMITATIONS.md','docs/PROOF_GUIDE.md','lean/README.md']:
        text=(ROOT/f).read_text(encoding='utf-8')
        require('v0.3.0-rc1' in text or f=='LIMITATIONS.md','Current version not explicit: '+f)
    status=read('release/CURRENT_STATUS.json')
    require(status['manuscript_version']=='v0.1-rc5' and status['lean_candidate']=='v0.3.0-rc1','Current status version drift')
    require(status['canonical_normalized_external_premises']==[] and status['physical_external_premises']==['E1','E2'],'Current premise drift')
    require(status['E3_canonical_dependency'] is False and status['identities']==accepted,'Current identity/premise mismatch')
    require(not status['published_release'],'Candidate incorrectly presented as published release')
    # Links in current-facing documents only. Original historical local links
    # are not retroactively made into public download promises.
    docs=['README.md','README.zh.md','CLAIMS.md','LIMITATIONS.md','AUTHORSHIP.md','docs/PROOF_GUIDE.md',
          'docs/VERSIONS.md','docs/UPGRADE_v0.3.0-rc1.md','docs/CONSISTENCY_AUDIT_v0.3.0-rc1.md',
          'docs/MATHEMATICAL_AUDIT_v0.3.0-rc1.md','paper/README.md','lean/README.md','lean/COVERAGE.md',
          'lean/CORRESPONDENCE.md','lean/GAP_MANIFEST.md','lean/CONTINUATION_SOURCE_CORRESPONDENCE.md',
          'lean/CONTINUATION_AUXILIARY_SCOPE.md','lean/tools/continuation/README.md',
          'lean/control_packet/continuation/README.md','lean/history/v0.2.1/README.md',
          'provenance/EXTERNAL_PREMISES.md']
    for name in docs:
        p=ROOT/name;require(p.is_file(),'Missing current-facing document: '+name)
        for target in re.findall(r'\[[^\]]*\]\(([^)]+)\)',p.read_text(encoding='utf-8')):
            if re.match(r'^[a-zA-Z]+:',target) or target.startswith('#'):continue
            target=target.split('#')[0].split('?')[0]
            require((p.parent/target).exists(),f'Broken current local link: {name} -> {target}')
    return {'protected_historical_files':len(baseline['protected_files']),'preserved_record_copies':len(hist['files']),
            'production_files_including_root':len(prod),'endpoint_count':18,'source_labels':len(new),
            'old_label_numbers_preserved':len(old),'proof_id':pid,
            'verification_id':identity(verification)}
def executed():
    v=read('release/next/VALIDATION.json')
    require(v['status']=='VERIFIED_CANDIDATE','Final validation not successful')
    require(v['identities']==read('lean/ci/accepted_identity.json'),'Receipt identity mismatch')
    sequence=read(v['clean_acceptance_sequence'])
    require(sequence['status']=='CHECK_SEQUENCE_PASSED_NOT_AUDIT_ROUND','Clean gate did not pass')
    require(all(sequence[k]==value for k,value in v['identities'].items()),'Clean gate bound different inputs')
    require(sequence['endpoint_count']==18 and sequence['fresh_kernel_replay_exit']==0,'Endpoint/replay mismatch')
    require(v['remaining_current_inconsistencies']==[],'Unresolved current inconsistencies')
    require(v['historical_diagnostics']['all_reproduced'],'Historical diagnostics not reproduced')
    require(v['new_checks']['exit_code']==0,'New checks did not run successfully')
    require(v['dependency_negative_control']['passed'],'Dependency negative control did not pass')
    for name,count in [('manifest-controls.json',13),('production-controls-13.json',13),('lean-controls-7.json',7)]:
        r=read('release/next/evidence/'+name)
        require(r['all_controls_pass'] and r['case_count']==count,'Control receipt mismatch: '+name)
    controls=read('release/next/evidence/lean-controls-7.json')
    require(controls['context']==v['identities'] and controls['context_unchanged'],'Lean control context changed')
    for c in controls['cases']:
        require(c['control_pass'] and sha(ROOT/'lean/control_packet/continuation/fixtures'/c['fixture'])==c['fixture_sha256'],'Control fixture changed')
    neg=read('release/next/evidence/unused-E3-control.json')
    require(neg['passed'] and neg['context_unchanged'] and neg['context']==v['identities'],'Unused-E3 control context mismatch')
    require(read('release/next/evidence/historical-diagnostics.json')['all_reproduced'],'Diagnostic receipt mismatch')
    require(read('release/next/evidence/new-mathematical-checks.json')['continuous_or_infinite_tail_certificate'] is False,'Finite checks overclaim an infinite certificate')
    idx=read('release/next/evidence/INDEX.json');archive=ROOT/'release/next/evidence'/idx['archive']
    require(sha(archive)==idx['sha256'] and archive.stat().st_size==idx['bytes'],'Execution archive identity mismatch')
    with tarfile.open(archive,'r:gz') as tar:
        members=tar.getmembers();expected={e['path']:e for e in idx['files']}
        require(len(members)==len(expected)==len(idx['files']),'Execution archive inventory mismatch')
        for member in members:
            require(member.isfile() and member.name in expected,'Unexpected archive entry: '+member.name)
            data=tar.extractfile(member).read();entry=expected[member.name]
            require(len(data)==entry['bytes'] and hashlib.sha256(data).hexdigest()==entry['sha256'],'Archived stream changed: '+member.name)
    return {'safe_project_declarations':sequence['audited_safe_declaration_count'],
            'fresh_kernel_replay_exit':0,'verified_archived_files':len(idx['files']),'status':v['status']}
def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--write-manifest',action='store_true',help='Snapshot the staged/tracked candidate; excludes this manifest itself.')
    a=p.parse_args()
    if a.write_manifest:
        (ROOT/MANIFEST).write_text(json.dumps({'schema':'ising-candidate-repository-v1',
          'manuscript':'v0.1-rc5','lean_candidate':'v0.3.0-rc1',
          'excludes':[MANIFEST],'files':inventory()},indent=2)+'\n',encoding='utf-8',newline='\n')
    result=semantic();result.update(executed())
    m=read(MANIFEST)
    require(m['schema']=='ising-candidate-repository-v1','Wrong current manifest schema')
    require(m['files']==inventory(),'Tracked candidate differs from its manifest')
    result.update(current_inventory_files=len(m['files']),manifest_excludes_itself=True)
    print(json.dumps(result,indent=2))
    return 0
if __name__=='__main__':
    try:raise SystemExit(main())
    except (OSError,RuntimeError,ValueError,KeyError,subprocess.SubprocessError) as e:
        print('CANDIDATE_CONSISTENCY_FAILED:',e,file=sys.stderr);raise SystemExit(1)
