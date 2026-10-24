#!/usr/bin/env python3
"""Execute clean ANISO/LT/HT builds, strict checks and separate fresh replays."""
import argparse,datetime,hashlib,json,os,platform,shutil,subprocess,sys,threading,time
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
PROJECT=ROOT/'lean'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()

def execute(label,argv,cwd,output):
    target=output/label
    target.mkdir(exist_ok=False)
    receipt=dict(argv=argv,cwd=str(cwd),started_utc=now())
    (target/'command.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print('START',label,json.dumps(argv),flush=True)
    start=time.monotonic()
    proc=subprocess.Popen(argv,cwd=cwd,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    lock=threading.Lock()
    with (target/'combined.log').open('wb') as combined:
        def capture(stream,name):
            with (target/name).open('wb') as log:
                while block:=stream.read1(65536):
                    log.write(block);log.flush()
                    with lock:combined.write(block);combined.flush()
        threads=[threading.Thread(target=capture,args=(proc.stdout,'stdout.log')),threading.Thread(target=capture,args=(proc.stderr,'stderr.log'))]
        for t in threads:t.start()
        code=proc.wait()
        for t in threads:t.join()
    receipt.update(exit_code=code,elapsed_seconds=time.monotonic()-start,finished_utc=now(),
        logs_sha256={p.name:sha(p) for p in target.glob('*.log')})
    (target/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print('FINISH',label,'exit',code,'seconds',round(receipt['elapsed_seconds'],2),flush=True)
    if code:
        print((target/'combined.log').read_text(errors='replace')[-5000:],flush=True)
        raise SystemExit(code)
    return receipt

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--only',choices=['all','aniso','lt','ht'],default='all')
    parser.add_argument('--max-compilers',type=int,choices=[1,2],default=2)
    args=parser.parse_args()
    output=args.output.resolve();output.mkdir(parents=True,exist_ok=False)
    for key in ['LEAN_PATH','LEAN_SRC_PATH']:
        assert not os.environ.get(key),f'Unexpected external {key}'
    existing=[p for p in PROJECT.rglob('*.olean') if '.lake/packages' not in p.relative_to(PROJECT).as_posix()]
    existing+=list((PROJECT/'.lake/build').rglob('*.olean'))
    assert not existing,f'Clean run requires zero candidate .olean files: {existing[:3]}'
    execute('pre-source-identity',[sys.executable,'scripts/verify_aniso_source_overlay.py'],ROOT,output)
    sources={p.relative_to(ROOT).as_posix():sha(p) for p in PROJECT.rglob('*')
             if p.is_file() and '.lake' not in p.relative_to(PROJECT).parts and
             (p.suffix in ['.lean','.toml'] or p.name in ['lean-toolchain','lake-manifest.json'])}
    packages=[]
    for package in json.loads((PROJECT/'lake-manifest.json').read_text())['packages']:
        path=PROJECT/'.lake/packages'/package['name']
        actual=subprocess.check_output(['git','-C',str(path),'rev-parse','HEAD'],text=True).strip()
        assert actual==package['rev'],f'Dependency revision mismatch: {package["name"]}'
        assert not subprocess.check_output(['git','-C',str(path),'status','--porcelain','--untracked-files=no'],text=True).strip()
        lib=path/'.lake/build/lib/lean'
        assert not list(lib.glob('IsingBulk*')) and not list(lib.glob('Audit*')),f'Project namespace in upstream cache: {path}'
        packages.append(dict(name=package['name'],revision=actual,tree=subprocess.check_output(['git','-C',str(path),'rev-parse','HEAD^{tree}'],text=True).strip()))
    binary=Path(shutil.which('lean')).resolve()
    toolchain=binary.parent.parent
    assert '4.34.1' in subprocess.check_output([str(binary),'--version'],text=True)
    identity=dict(started_utc=now(),platform=platform.platform(),python=sys.version,
        lean_version=subprocess.check_output([str(binary),'--version'],text=True).strip(),
        lake_version=subprocess.check_output(['lake','--version'],text=True).strip(),
        binaries={name:dict(path=str(toolchain/'bin'/name),sha256=sha(toolchain/'bin'/name)) for name in ['lean','lake','leanchecker']},
        checkout_commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
        checkout_tree=subprocess.check_output(['git','rev-parse','HEAD^{tree}'],cwd=ROOT,text=True).strip(),
        git_status=subprocess.check_output(['git','status','--porcelain'],cwd=ROOT,text=True),
        github_sha=os.environ.get('GITHUB_SHA'),pr_head_sha=os.environ.get('PR_HEAD_SHA'),
        project_olean_count_before=0,source_sha256=sources,packages=packages)
    # Lake has no compilation-jobs flag in this pinned release. Its documented
    # LEAN_SYSROOT override selects a shim with unchanged official libraries.
    # A flock semaphore bounds real compiler processes; every real argv is logged.
    shim=output/'toolchain';(shim/'bin').mkdir(parents=True)
    for item in toolchain.iterdir():
        if item.name!='bin':(shim/item.name).symlink_to(item,target_is_directory=item.is_dir())
    for item in (toolchain/'bin').iterdir():
        if item.name!='lean':(shim/'bin'/item.name).symlink_to(item)
    wrapper=shim/'bin/lean'
    wrapper.write_text('#!/usr/bin/env python3\nimport runpy\nrunpy.run_path('+repr(str(ROOT/'scripts/limit_lean_compilation.py'))+',run_name="__main__")\n')
    wrapper.chmod(0o755)
    slots=output/'compiler-slots';slots.mkdir()
    os.environ.update(LEAN_SYSROOT=str(shim),LAKE_OVERRIDE_LEAN='true',ANISO_REAL_LEAN=str(binary),
        ANISO_COMPILER_SLOTS=str(slots),ANISO_MAX_COMPILERS=str(args.max_compilers),
        LEAN_NUM_THREADS='2',RAYON_NUM_THREADS='2',LAKE_NO_CACHE='true',LAKE_ARTIFACT_CACHE='false')
    identity.update(environment={k:os.environ[k] for k in ['LEAN_SYSROOT','LAKE_OVERRIDE_LEAN','LEAN_NUM_THREADS','LAKE_NO_CACHE','LAKE_ARTIFACT_CACHE','ANISO_MAX_COMPILERS']},compiler_wrapper_sha256=sha(wrapper),compiler_limiter_sha256=sha(ROOT/'scripts/limit_lean_compilation.py'))
    (output/'runtime-and-source-identity.json').write_text(json.dumps(identity,indent=2)+'\n')
    commands=[]
    for phase,config,root,audit in [('aniso','lakefile.anisotropic.toml','IsingBulkAnisotropic','AuditAnisotropic'),('lt','lakefile.toml','IsingBulk','Audit'),('ht','lakefile.ht.toml','IsingBulkHT','AuditHT')]:
        if args.only not in ['all',phase]:continue
        commands += [(phase+'-build',['lake','-f',config,'-R','-H','build',root,audit]),
                     (phase+'-strict-audit',['lake','-f',config,'env','lean','-j1','-DwarningAsError=true',audit+'.lean']),
                     (phase+'-fresh-replay',['lake','-f',config,'env','leanchecker','--fresh','--verbose',root])]
        if phase=='aniso':
            commands.append(('aniso-closure-audit',['lake','-f',config,'env','lean','-j1','-DwarningAsError=true','AuditAnisotropicClosure.lean']))
            for control in ['Nonvacuity','CompleteScope','PhysicalConventions']:
                commands.append(('aniso-control-'+control,['lake','-f',config,'env','lean','-j1','-DwarningAsError=true','IsingBulk/Anisotropic/Controls/'+control+'.lean']))
    receipts=[]
    try:
        for label,argv in commands:receipts.append(execute(label,argv,PROJECT,output))
        assert all(sha(ROOT/p)==h for p,h in sources.items()),'Project source changed during run'
        execute('post-publication-identity',[sys.executable,'scripts/verify_three_proof_publication.py'],ROOT,output)
    finally:
        (output/'SUMMARY.json').write_text(json.dumps(dict(completed_commands=len(receipts),required_commands=len(commands),receipts=receipts,finished_utc=now()),indent=2)+'\n')
    print('PASS: all selected gates executed on the captured source',flush=True)

if __name__=='__main__':main()
