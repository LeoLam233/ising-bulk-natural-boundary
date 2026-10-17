"""Attack the candidate guard in an isolated clone; never mutate the input tree."""
import argparse, csv, hashlib, io, json, pathlib, shutil, subprocess, sys, tempfile

ROOT=pathlib.Path(__file__).resolve().parents[2]
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--output',type=pathlib.Path,required=True)
args=parser.parse_args()
assert not args.output.exists(),'Use a fresh result path'

def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def git(cwd,*argv):
    return subprocess.check_output(['git','-c','safe.directory=*',*argv],cwd=cwd)
critical=['lean/ci/accepted_identity.json','checks/amplitude_identification/check_amplitude.py',
          'checks/amplitude_identification/repository_controls.py',
          'scripts/verify_candidate.py','lean/source_snapshot/manuscript-rc5.tex',
          'docs/UPGRADE_v0.3.0-rc1.md','lean/IsingBulk/Algebra/NickelOrder.lean',
          'lean/CLAIM_LEDGER.tsv']
before={name:digest(ROOT/name) for name in critical}
def input_inventory():
    names=git(ROOT,'ls-files','--cached','--others','--exclude-standard','-z').decode().split('\0')
    return {name:digest(ROOT/name) for name in sorted(set(names)-{''})}
tree_before=input_inventory()
scratch=ROOT/'.local';scratch.mkdir(exist_ok=True)
work=pathlib.Path(tempfile.mkdtemp(prefix='rc2-repository-controls-',dir=scratch))
clone=work/'repo'
git(ROOT,'clone','--quiet','--no-hardlinks','--no-checkout',str(ROOT),str(clone))
paths=git(ROOT,'ls-files','--cached','--others','--exclude-standard','-z').decode().split('\0')
for name in sorted(set(paths)-{''}):
    rel=pathlib.Path(name)
    assert not rel.is_absolute() and '..' not in rel.parts and '.git' not in rel.parts
    source=ROOT/rel;target=clone/rel
    assert source.is_file() and not source.is_symlink()
    assert target.resolve().is_relative_to(clone)
    target.parent.mkdir(parents=True,exist_ok=True)
    shutil.copyfile(source,target)
git(clone,'add','--all')

def invoke(name,write_manifest=True):
    argv=[sys.executable,'-B','scripts/verify_candidate.py']
    if write_manifest:argv.append('--write-manifest')
    result=subprocess.run(argv,cwd=clone,capture_output=True,text=True,encoding='utf-8',timeout=90)
    (work/(name+'.stdout')).write_text(result.stdout,encoding='utf-8',newline='\n')
    (work/(name+'.stderr')).write_text(result.stderr,encoding='utf-8',newline='\n')
    return dict(argv=argv,cwd=str(clone),exit_code=result.returncode,
                stdout=result.stdout,stderr=result.stderr)

positive=invoke('positive_before')
assert positive['exit_code']==0,positive
cases=[]
def negative(name,path,mutate,expected,write_manifest=True):
    target=clone/path;original=target.read_bytes()
    try:
        target.write_bytes(mutate(original))
        record=invoke(name,write_manifest)
        # A timeout/import/resource error is never an accepted negative.
        passed=record['exit_code']==1 and expected in record['stderr']
        record.update(name=name,mutated_path=path,expected_diagnostic=expected,control_pass=passed)
        cases.append(record)
        assert passed,record
    finally:
        target.write_bytes(original)

negative('retained_rc5_snapshot','lean/source_snapshot/manuscript-rc5.tex',
         lambda b:b+b'\n% isolated preservation attack\n','Retained rc5 snapshot/report changed:')
negative('retained_rc1_report','docs/UPGRADE_v0.3.0-rc1.md',
         lambda b:b+b'\nIsolated historical-report attack.\n','Retained rc5 snapshot/report changed:')
negative('production_source','lean/IsingBulk/Algebra/NickelOrder.lean',
         lambda b:b+b'\n-- isolated production-source attack\n','Production Lean source differs from the verified predecessor:')
def formalize_by_label(data):
    reader=csv.DictReader(io.StringIO(data.decode()),delimiter='\t')
    fields=reader.fieldnames;rows=list(reader)
    for row in rows:
        if row['source_label']=='prop:amplitudecomparison':row['status']='PROVED'
    stream=io.StringIO(newline='')
    writer=csv.DictWriter(stream,fieldnames=fields,delimiter='\t',quoting=csv.QUOTE_ALL,lineterminator='\n')
    writer.writeheader();writer.writerows(rows)
    return stream.getvalue().encode()
negative('fake_formal_amplitude','lean/CLAIM_LEDGER.tsv',formalize_by_label,
         'Literature identity incorrectly presented as a Lean export')
def old_manifest(data):
    value=json.loads(data);value['manuscript']='v0.1-rc5'
    return (json.dumps(value,indent=2)+'\n').encode()
# Reset manifest after restoring the last mutation before testing its header.
assert invoke('manifest_reset')['exit_code']==0
negative('old_manifest_version','release/next/MANIFEST.json',old_manifest,
         'Current manifest version drift',False)
positive_after=invoke('positive_after')
assert positive_after['exit_code']==0,positive_after
after={name:digest(ROOT/name) for name in critical}
assert before==after,'Input candidate changed during isolated controls'
tree_after=input_inventory()
assert tree_before==tree_after,'Tracked/unignored input tree changed during isolated controls'
tree_id=lambda value:hashlib.sha256(json.dumps(value,sort_keys=True,separators=(',',':')).encode()).hexdigest()
result=dict(all_controls_pass=True,case_count=len(cases),cases=cases,
            positive_before=positive,positive_after=positive_after,
            context=json.loads((ROOT/'lean/ci/accepted_identity.json').read_text()),
            input_tree_unchanged=tree_before==tree_after,input_file_sha256=before,
            input_tree_files=len(tree_before),input_tree_before_id=tree_id(tree_before),
            input_tree_after_id=tree_id(tree_after),
            tree_check_scope='All tracked/unignored file bytes before and after this run; ignored throwaway clones/results excluded. Later receipt assembly may change metadata while the separately listed critical inputs remain bound.',
            isolated_workspace=str(work),
            scope='Repository provenance/version/formal-scope controls, not new mathematical proofs or kernel checks.')
args.output.parent.mkdir(parents=True,exist_ok=True)
args.output.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps({'all_controls_pass':True,'case_count':len(cases),
                  'input_tree_unchanged':True,'isolated_workspace':str(work)},indent=2))
