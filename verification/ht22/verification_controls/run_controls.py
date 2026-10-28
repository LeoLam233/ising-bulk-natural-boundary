#!/usr/bin/env python3
"""Author-built HT22 control runner. Development is never final acceptance.

Final mode requires an independently frozen source manifest plus COMPLETE
RootWalker reports for the actual aggregate and deliberate old-route bypass.
Heavy graph extraction / clean builds are not performed by this runner.
"""
import argparse,datetime,hashlib,json,os,pathlib,re,subprocess,sys
HERE=pathlib.Path(__file__).resolve().parent
CAMPAIGN=HERE.parent
FIXTURES=HERE/'fixtures'
COMPILER=CAMPAIGN/'runtime/compile_module.py'
MODULES=['IsingBulk.HT22.Controls.'+s for s in ('Basic','Scope','FiniteTruncation')]
NEGATIVE=['ZeroPhysics','OmittedOrigin','ZeroObservable','ZeroCoupling','FiniteSubstitution']

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()

def input_digest(value):
    digest=value.get('sha256') if isinstance(value,dict) else value
    if not isinstance(digest,str) or not re.fullmatch(r'[0-9a-f]{64}',digest):
        raise ValueError('malformed SHA256 in frozen manifest')
    return digest

def mandatory_inputs(campaign=CAMPAIGN):
    controls=campaign/'verification_controls'
    paths=list((campaign/'repository/lean/IsingBulk/HT22').rglob('*.lean'))
    paths+=list((controls/'fixtures').glob('*.lean'))+list(controls.glob('*.py'))
    paths+=[campaign/s for s in (
        'repository/lean/IsingBulk/HT22.lean','repository/lean/IsingBulkHT22.lean',
        'repository/lean/AuditHT22.lean','repository/lean/lakefile.ht22.toml',
        'repository/lean/lean-toolchain','repository/lean/lake-manifest.json',
        'repository/verification/lt22/RootWalker.lean')]
    return {str(p.relative_to(campaign)) for p in paths}

def read_manifest(path):
    raw=path.read_bytes();manifest=json.loads(raw)
    files=manifest['files']
    if not isinstance(files,dict) or not files:raise ValueError('empty/malformed frozen manifest')
    return hashlib.sha256(raw).hexdigest(),{name:input_digest(value) for name,value in files.items()}

def check_manifest(path,manifest_sha,files,final=False,campaign=CAMPAIGN):
    if sha(path)!=manifest_sha:raise ValueError('frozen manifest changed during check')
    if final and not mandatory_inputs(campaign)<=set(files):
        raise ValueError('frozen manifest omits source/control inputs: '+
                         ','.join(sorted(mandatory_inputs(campaign)-set(files))))
    for name,expected in files.items():
        if not isinstance(name,str) or pathlib.Path(name).is_absolute():
            raise ValueError('manifest path is not campaign-relative: '+str(name))
        q=(campaign/name).resolve();q.relative_to(campaign)
        if sha(q)!=expected:raise ValueError('frozen source mismatch: '+name)

def prepare_portable_overlay(destination,lean_path):
    """Merge namespace ancestors, not whole trees; all borrowed files are links.

    Lean resolves a top-level namespace in the FIRST LEAN_PATH root containing
    it, so a sparse IsingBulk output directory hides all other IsingBulk objects.
    Materialize only IsingBulk/HT22/Controls and shallow-link its siblings.
    """
    roots=[pathlib.Path(x).resolve() for x in lean_path.split(os.pathsep) if x]
    if not roots or any(not p.is_dir() for p in roots):raise ValueError('invalid portable LEAN_PATH root')
    destination.mkdir(parents=True,exist_ok=False)
    route=('IsingBulk','HT22','Controls')
    stems={m.rsplit('.',1)[1] for m in MODULES}
    def merge(dest,sources,depth):
        entries={}
        for source in sources:
            for child in sorted(source.iterdir()):entries.setdefault(child.name,child)
        branch=route[depth] if depth<len(route) else None
        for name,child in entries.items():
            if name==branch or (branch is None and name.split('.',1)[0] in stems):continue
            (dest/name).symlink_to(child.resolve(),target_is_directory=child.is_dir())
        if branch:
            next_dest=dest/branch;next_dest.mkdir()
            merge(next_dest,[source/branch for source in sources if (source/branch).is_dir()],depth+1)
    merge(destination,roots,0)

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--phase',choices=['development','final'],default='development')
    p.add_argument('--frozen-manifest',type=pathlib.Path,
                   help='JSON object {files: {campaign-relative path: sha256}}; includes all proof source/config inputs')
    p.add_argument('--final-root',default='IsingBulk.HT22.ht22_full_target')
    p.add_argument('--final-graph-base',type=pathlib.Path)
    p.add_argument('--bypass-graph-base',type=pathlib.Path)
    p.add_argument('--no-deps',action='store_true',help='Use only when final clean built dependencies already exist')
    p.add_argument('--lean',type=pathlib.Path,help='Portable mode: exact pinned Lean binary; no runtime helper used')
    p.add_argument('--lean-path',help='Portable mode: LEAN_PATH for already clean-built project and pinned upstream libraries')
    p.add_argument('--require',action='append',default=[],help='Additional required reachable mechanism declaration')
    a=p.parse_args()
    if bool(a.lean)!=bool(a.lean_path):p.error('--lean and --lean-path must be supplied together')
    if a.phase=='final' and not all((a.frozen_manifest,a.final_graph_base,a.bypass_graph_base)):
        p.error('final requires --frozen-manifest --final-graph-base --bypass-graph-base')
    stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    out=HERE/'runs'/(stamp+'_'+a.phase);out.mkdir(parents=True,exist_ok=False)
    records=[]
    env=os.environ.copy()
    def module_command(mod):
        if not a.lean:
            return [sys.executable,str(COMPILER)]+([] if a.no_deps else ['--deps'])+[mod]
        src=CAMPAIGN/'repository/lean'/pathlib.Path(*mod.split('.')).with_suffix('.lean')
        obj=out/'lib/lean'/pathlib.Path(*mod.split('.')).with_suffix('.olean')
        obj.parent.mkdir(parents=True,exist_ok=True)
        return [str(a.lean),'-j1','-DwarningAsError=true','--root',str(CAMPAIGN/'repository/lean'),'-o',str(obj),str(src)]
    def fixture_command(name):
        src=FIXTURES/(name+'.lean')
        if not a.lean:return [sys.executable,str(COMPILER),'--check-file',str(src)]
        return [str(a.lean),'-j1','-DwarningAsError=true','--root',str(FIXTURES),str(src)]
    manifest_sha=None;manifest_files=None;lean_sha=None;graph_inputs={}
    def verify_frozen():
        if a.frozen_manifest is None:return
        check_manifest(a.frozen_manifest,manifest_sha,manifest_files,a.phase=='final')
    try:
        if a.frozen_manifest:manifest_sha,manifest_files=read_manifest(a.frozen_manifest)
        verify_frozen()
        for base in (a.final_graph_base,a.bypass_graph_base):
            if base:
                for suffix in ('.graph.jsonl','.types.jsonl','.summary.json'):
                    path=pathlib.Path(str(base)+suffix);graph_inputs[str(path)]=sha(path)
        if a.lean:
            lean_sha=sha(a.lean)
            prepare_portable_overlay(out/'lib/lean',a.lean_path)
            env['LEAN_PATH']=str(out/'lib/lean')+os.pathsep+a.lean_path
            env['LEAN_NUM_THREADS']='1'
    except (OSError,ValueError,KeyError,TypeError) as e:
        (out/'receipt.json').write_text(json.dumps(dict(phase=a.phase,accepted=False,
            independent_audit=False,final_controls_passed=False,preflight_error=str(e)),indent=2)+'\n')
        print(str(e),file=sys.stderr);print('Receipt: '+str(out/'receipt.json'));return 2
    # Pin every local control input even during development. Final source
    # verification additionally pins the complete external frozen manifest.
    control_inputs={str(p.relative_to(CAMPAIGN)):sha(p) for p in
                    list((CAMPAIGN/'repository/lean/IsingBulk/HT22/Controls').glob('*.lean'))+
                    list(FIXTURES.glob('*.lean'))+list(HERE.glob('*.py'))}
    def run(label,cmd,expect=0,diagnostic=None):
        started=datetime.datetime.now(datetime.timezone.utc).isoformat()
        proc=subprocess.run(cmd,cwd=CAMPAIGN,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        (out/(label+'.stdout.log')).write_text(proc.stdout)
        (out/(label+'.stderr.log')).write_text(proc.stderr)
        ok=proc.returncode==expect
        if diagnostic is not None:ok=ok and diagnostic in (proc.stdout+proc.stderr)
        rec=dict(label=label,cmd=cmd,started_utc=started,exit_code=proc.returncode,
                 expected_exit_code=expect,passed=ok,
                 diagnostic_required=diagnostic)
        records.append(rec)
        print(label+': '+('PASS' if ok else 'FAIL')+' (exit '+str(proc.returncode)+')',flush=True)
        return ok
    prerequisite_ok=True
    for mod in MODULES:
        if not run(mod.split('.')[-1],module_command(mod)):
            prerequisite_ok=False;break
    if prerequisite_ok:
        run('PositiveAxioms',fixture_command('PositiveAxioms'))
        printed=(out/'PositiveAxioms.stdout.log').read_text()
        declarations=re.findall(r'^#print axioms (\S+)',(FIXTURES/'PositiveAxioms.lean').read_text(),re.M)
        printed_axioms=re.findall(r"'([^']+)' depends on axioms:\s*\[(.*?)\]",printed,re.S)
        observed={x.strip() for _,block in printed_axioms for x in block.split(',') if x.strip()}
        observed_names=[name for name,_ in printed_axioms]
        axiom_ok=(sorted(observed_names)==sorted(declarations) and bool(declarations) and
                  observed<={'propext','Classical.choice','Quot.sound'})
        records.append(dict(label='PositiveAxiomsWhitelist',passed=axiom_ok,
                            observed_axioms=sorted(observed),observed_declarations=observed_names))
        for name in NEGATIVE:
            run(name,fixture_command(name),
                expect=1,diagnostic='Type mismatch')
        run('OldRouteBypass_kernel_acceptance',fixture_command('OldRouteBypass'))
    run('RoutePolicyUnitControls',[sys.executable,str(HERE/'test_route_policy.py')])
    run('ControlsRunnerUnitControls',[sys.executable,str(HERE/'test_controls_runner.py')])
    if a.final_graph_base:
        run('ActualFinalRoute',[sys.executable,str(HERE/'route_policy.py'),str(a.final_graph_base),
                                '--root',a.final_root,'--physical']+
                                [item for name in a.require for item in ('--require',name)])
    if a.bypass_graph_base:
        run('OldRouteBypass_policy_rejection',[sys.executable,str(HERE/'route_policy.py'),str(a.bypass_graph_base),
                                              '--root','AuditSentinel.oldRouteBypass'],expect=1,
                                              diagnostic='forbidden old proof-route reachables')
    stability=[]
    for name,expected in control_inputs.items():
        try:
            if sha(CAMPAIGN/name)!=expected:stability.append(name)
        except OSError as e:stability.append(str(e))
    for name,expected in graph_inputs.items():
        try:
            if sha(pathlib.Path(name))!=expected:stability.append('graph changed: '+name)
        except OSError as e:stability.append(str(e))
    if a.lean:
        try:
            if sha(a.lean)!=lean_sha:stability.append('Lean binary changed')
        except OSError as e:stability.append(str(e))
    try:verify_frozen()
    except (OSError,ValueError,KeyError,TypeError) as e:stability.append(str(e))
    accepted=prerequisite_ok and all(r['passed'] for r in records) and not stability
    receipt=dict(phase=a.phase,accepted=accepted,independent_audit=False,
                 final_controls_passed=a.phase=='final' and accepted,
                 portable_lean_binary=str(a.lean) if a.lean else None,
                 portable_lean_binary_sha256=lean_sha,
                 lean_path=env.get('LEAN_PATH'),
                 frozen_manifest=str(a.frozen_manifest) if a.frozen_manifest else None,
                 frozen_manifest_sha256=manifest_sha,
                 graph_inputs=graph_inputs,required_extra=a.require,
                 control_inputs=control_inputs,source_changed_during_check=stability,records=records,
                 scope='Effective author-built controls only; not clean build or fresh kernel replay.',
                 mandatory_deferred=[] if a.phase=='final' else ['Final identical frozen source rerun',
                    'Complete RootWalker proof-term/structural-support reports for aggregate and old-route bypass'])
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print('Receipt: '+str(out/'receipt.json'))
    return 0 if accepted else 1
if __name__=='__main__':sys.exit(main())
