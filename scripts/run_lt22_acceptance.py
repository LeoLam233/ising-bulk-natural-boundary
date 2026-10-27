#!/usr/bin/env python3
"""Fresh integration acceptance of the immutable Preferred22 route (Linux/WSL)."""
import argparse, collections, datetime, hashlib, json, os, pathlib, re, shutil, subprocess, sys, time

ROOT = pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'scripts'))
from verify_lt22_publication import verify

def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
    return h.hexdigest()

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--output',required=True);parser.add_argument('--source-bundle',action='store_true');a=parser.parse_args()
    out=pathlib.Path(a.output).resolve();out.mkdir(parents=True,exist_ok=False)
    project=ROOT/'lean'
    env=os.environ.copy()
    env.update(LEAN_NUM_THREADS='2',RAYON_NUM_THREADS='2',LAKE_ARTIFACT_CACHE='false',LAKE_NO_CACHE='true')
    commands=[]
    def save(name,value): (out/name).write_text(json.dumps(value,indent=2)+'\n')
    def run(label,cmd,cwd=project,extra=None):
        start=datetime.datetime.now(datetime.timezone.utc).isoformat(); t=time.monotonic()
        e=env.copy();e.update(extra or {})
        receipt=dict(command=cmd,cwd=str(cwd),started_utc=start)
        save(label+'.command.json',receipt)
        with (out/(label+'.stdout.log')).open('wb') as stdout,(out/(label+'.stderr.log')).open('wb') as stderr:
            code=subprocess.call(cmd,cwd=cwd,env=e,stdout=stdout,stderr=stderr)
        receipt.update(exit_code=code,ended_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),elapsed_seconds=time.monotonic()-t,
                       stdout_sha256=sha(out/(label+'.stdout.log')),stderr_sha256=sha(out/(label+'.stderr.log')))
        save(label+'.receipt.json',receipt);commands.append(receipt)
        print(label+': exit '+str(code),flush=True)
        if code: raise RuntimeError(label+' failed; see raw streams')
        return (out/(label+'.stdout.log')).read_text(errors='replace')
    try:
        identity=verify(a.source_bundle);save('SOURCE_IDENTITY.json',identity)
        if not a.source_bundle: run('01-preservation',[sys.executable,str(ROOT/'scripts/verify_lt22_preservation.py')],ROOT)
        versions={name:run('02-'+name,[name,'--version']).strip() for name in ('lean','lake')}
        assert '4.34.1' in versions['lean'] and '5045d0056413266e57c625dcd7c365b10e377c52' in versions['lean']
        bins={name:dict(path=shutil.which(name),sha256=sha(pathlib.Path(shutil.which(name)))) for name in ('lean','lake','leanchecker')}
        expected_bins={'lean':'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550','lake':'6f53827dab18010d6c690d14c8401cacabc1db958edb3552a877ed4cf1dd995d','leanchecker':'ccef1bfe9bfeecea65137d94a69033c1a89f360711f50fa3178e7ba3e696fcbe'}
        assert {k:v['sha256'] for k,v in bins.items()}==expected_bins,bins
        dependencies=[]
        for name,rev in identity['dependency_pins'].items():
            p=project/'.lake/packages'/name
            actual=run('03-head-'+name,['git','-c','safe.directory='+str(p.resolve()),'rev-parse','HEAD'],p).strip()
            assert actual==rev,(name,actual,rev)
            status=run('03-status-'+name,['git','-c','safe.directory='+str(p.resolve()),'status','--porcelain','--untracked-files=no'],p)
            assert not status.strip(),(name,status)
            foreign=[f for f in p.rglob('*.olean*') if 'IsingBulk' in f.relative_to(p).parts or f.name.startswith('IsingBulk')]
            assert not foreign,('Foreign project objects',name,[str(f) for f in foreign[:5]])
            dependencies.append(dict(name=name,rev=rev,tracked_tree_clean=True))
        save('ENVIRONMENT.json',dict(platform=sys.platform,python=sys.version,versions=versions,binaries=bins,dependencies=dependencies,
                                   environment={k:env[k] for k in ('LEAN_NUM_THREADS','RAYON_NUM_THREADS','LAKE_ARTIFACT_CACHE','LAKE_NO_CACHE')},
                                   github_sha=os.environ.get('GITHUB_SHA'),github_head_sha=os.environ.get('PR_HEAD_SHA'),github_run_id=os.environ.get('GITHUB_RUN_ID')))
        # Only project products are removed. Pinned third-party cache is retained.
        build=project/'.lake/build'
        assert build.resolve().is_relative_to(project.resolve())
        if build.exists(): shutil.rmtree(build)
        assert not build.exists()
        assert not list((project/'IsingBulk').rglob('*.olean'))
        save('CLEAN_PREFLIGHT.json',dict(project_build_absent=True,source_tree_objects=0,cache_scope='pinned third-party packages only'))
        text=run('04-clean-build',['lake','--no-cache','--no-ansi','-v','-f','lakefile.toml','build','IsingBulk.Preferred22'])
        inv=re.findall(r'/IsingBulk/([^\s]+)\.lean -o ',text)
        inv=['IsingBulk.'+p.replace('/','.') for p in inv]
        expected={k[len('lean/'):-5].replace('/','.') for k in identity['source_sha256'] if k.startswith('lean/IsingBulk/') and k.endswith('.lean')}
        # The root is under IsingBulk/Preferred22.lean, included in the same pattern.
        built=re.findall(r'\bBuilt (IsingBulk[.A-Za-z0-9_]+)\s',text)
        replay=re.findall(r'\bReplayed IsingBulk[. ]',text)
        summary=dict(expected=len(expected),compiler_invocations=len(inv),unique_compiler_invocations=len(set(inv)),
                     unique_built_events=len(set(built)),local_replays=len(replay),missing_compilers=sorted(expected-set(inv)),extra_compilers=sorted(set(inv)-expected))
        save('CLEAN_BUILD.json',summary)
        assert len(expected)==len(inv)==len(set(inv))==len(set(built))==486 and not replay and set(inv)==expected,summary
        probe=out/'probe';probe.mkdir()
        for name in ('RootWalker.lean','RootProbe.lean'):shutil.copyfile(ROOT/'verification/lt22'/name,probe/name)
        run('05-walker',['lean','-j1','-DwarningAsError=true','-o','RootWalker.olean','RootWalker.lean'],probe)
        # lake env sets the project's import path, then the probe directory is prepended inside Python.
        driver=probe/'run_probe.py'
        driver.write_text('import os,subprocess,sys\nos.environ["LEAN_PATH"]=sys.argv[1]+os.pathsep+os.environ.get("LEAN_PATH","")\nos.chdir(sys.argv[1])\nsys.exit(subprocess.call(["lean","-j1","-DwarningAsError=true","RootProbe.lean"]))\n')
        run('06-terminal-type-and-closure',['lake','env',sys.executable,str(driver),str(probe)])
        rows=[json.loads(s) for s in (probe/'root.graph.jsonl').read_text().splitlines()]
        old=json.loads((ROOT/'provenance/lt22/AUDITED_GRAPH.json').read_text())
        digest=hashlib.sha256(json.dumps(sorted(rows,key=lambda r:r['name']),sort_keys=True,separators=(',',':')).encode()).hexdigest()
        closure=json.loads((probe/'root.summary.json').read_text())
        root_type=next(json.loads(s) for s in (probe/'root.types.jsonl').read_text().splitlines() if json.loads(s)['name']==old['root'])
        assert root_type['pretty_type']=='IsingBulk.Preferred22.PreferredFullTarget',root_type
        assert closure['root']==old['root'] and not closure['missing'] and not closure['unsafe_or_partial']
        assert sorted(closure['axioms'])==old['axioms']==['Classical.choice','Quot.sound','propext']
        assert digest==old['canonical_graph_sha256'],('Stored closure differs from audited graph',digest)
        closure.update(canonical_graph_sha256=digest,exact_audited_dependency_graph=True,forbidden_old_endpoint_dependencies=0,root_type='IsingBulk.Preferred22.PreferredFullTarget',root_premises=0)
        save('CLOSURE.json',closure)
        before={p.relative_to(build).as_posix():sha(p) for p in build.rglob('*.olean*') if p.is_file()}
        save('PROOF_OBJECT_SHA256.json',before)
        run('07-official-fresh-kernel',['lake','env','leanchecker','--fresh','--verbose','IsingBulk.Preferred22'])
        after={p.relative_to(build).as_posix():sha(p) for p in build.rglob('*.olean*') if p.is_file()}
        assert before==after,'Kernel replay changed proof objects'
        verify(a.source_bundle)
        save('SUMMARY.json',dict(status='PASS',clean_build=summary,closure=closure,official_fresh_kernel_exit_code=0,proof_objects_unchanged=True,
                                protected_files_unchanged=True if not a.source_bundle else None,scope='source-closure reproduction' if a.source_bundle else 'combined-repository acceptance',commands=len(commands),source_manifest_sha256=sha(ROOT/'provenance/lt22/SOURCE_IDENTITY.json')))
        print('PASS: clean integrated build, exact terminal type/axioms/audited graph, fresh official kernel replay, protected files',flush=True)
    except BaseException as exc:
        save('SUMMARY.json',dict(status='FAIL',error=str(exc),completed_commands=len(commands)))
        raise

if __name__=='__main__':main()
