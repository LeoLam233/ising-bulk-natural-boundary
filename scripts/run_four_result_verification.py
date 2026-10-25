#!/usr/bin/env python3
"""Execute one source-clean integrated root, strict closure, controls and fresh replay."""
import argparse,datetime,hashlib,json,os,platform,re,shutil,subprocess,sys,threading,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];PROJECT=ROOT/'lean'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
now=lambda:datetime.datetime.now(datetime.timezone.utc).isoformat()
PHASES={
 'joint':('lakefile.joint.toml','IsingBulkJoint','AuditJoint','IsingBulk.Joint.full_joint_conclusion',[
   'IsingBulk.Joint.PhysicalField.PublishedRealSpinFamily','IsingBulk.Joint.PhysicalField.PublishedRealGibbsFamily']),
 'lt':('lakefile.toml','IsingBulk','Audit','IsingBulk.Final.theorem_nb_physical',[
   'IsingBulk.Final.PhysicalSusceptibilityE1','IsingBulk.Final.YangMagnetizationE2']),
 'ht':('lakefile.ht.toml','IsingBulkHT','AuditHT','IsingBulk.HT.Final.publishedPhysicalSusceptibility_germ_natural_boundary',[
   'IsingBulk.HT.Final.PublishedAngularSusceptibilityRepresentation']),
 'aniso':('lakefile.anisotropic.toml','IsingBulkAnisotropic','AuditAnisotropic','IsingBulk.Anisotropic.full_uniform_field_conclusion',[
   'IsingBulk.Anisotropic.FormFactors.PublishedRealSpinFormFactors','IsingBulk.Anisotropic.PhysicalField.PublishedRealGibbsFields'])}

def execute(label,argv,cwd,output,expected=None,expected_line=None):
    dest=output/label;dest.mkdir();record={'label':label,'argv':argv,'cwd':str(cwd),'started_utc':now(),
      'expected_exit':1 if expected else 0,'expected_diagnostic':expected,'expected_line':expected_line}
    (dest/'command.json').write_text(json.dumps(record,indent=2)+'\n')
    print('START',label,json.dumps(argv),flush=True);start=time.monotonic()
    proc=subprocess.Popen(argv,cwd=cwd,stdout=subprocess.PIPE,stderr=subprocess.PIPE);lock=threading.Lock()
    with (dest/'combined.log').open('wb') as combined:
        def capture(stream,name):
            with (dest/name).open('wb') as f:
                while block:=stream.read1(65536):
                    f.write(block);f.flush()
                    with lock:combined.write(block);combined.flush()
        threads=[threading.Thread(target=capture,args=(proc.stdout,'stdout.log')),threading.Thread(target=capture,args=(proc.stderr,'stderr.log'))]
        for t in threads:t.start()
        code=proc.wait()
        for t in threads:t.join()
    text=(dest/'stdout.log').read_text(errors='replace');err=(dest/'stderr.log').read_text(errors='replace')
    passed=code==0
    if expected:
        errors=re.findall(r'^(.+?\.lean):(\d+):(\d+): error(?:\([^)]*\))?: (.*)$',text,re.M)
        infra=re.search(r'unknown (module|identifier|constant|tactic)|invalid import|no such file|failed to load|out of memory|heartbeats|timeout|stack overflow|unexpected token',text+err,re.I)
        passed=code==1 and bool(errors) and not err and not infra and all(
          re.search(expected,msg) and (expected_line is None or int(line)==expected_line)
          for _,line,_,msg in errors)
    record.update(exit_code=code,passed=passed,finished_utc=now(),elapsed_seconds=time.monotonic()-start,
      logs_sha256={p.name:sha(p) for p in dest.glob('*.log')})
    (dest/'receipt.json').write_text(json.dumps(record,indent=2)+'\n')
    print('FINISH',label,'exit',code,'passed',passed,'seconds',round(record['elapsed_seconds'],2),flush=True)
    if not passed:
        print((dest/'combined.log').read_text(errors='replace')[-6000:],flush=True)
        raise RuntimeError('Mandatory gate failed: '+label)
    return record

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--only',choices=PHASES,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--max-compilers',type=int,choices=[1,2,3,4],default=2);a=p.parse_args()
    out=a.output.resolve();assert not out.is_relative_to(ROOT),'Receipts must be outside the source tree';out.mkdir(parents=True,exist_ok=False)
    for key in ['LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT']:assert not os.environ.get(key),'Unexpected external '+key
    existing=[p for p in PROJECT.rglob('*.olean') if '.lake/packages' not in p.relative_to(PROJECT).as_posix()]
    preflight={'project_olean_count_before':len(existing),'preexisting_project_oleans':[str(p) for p in existing]}
    (out/'CLEAN_SOURCE_PREFLIGHT.json').write_text(json.dumps(preflight,indent=2)+'\n');assert not existing,'Candidate objects already present'
    records=[];config,root,audit,endpoint,required=PHASES[a.only]
    run=lambda label,argv,cwd=PROJECT,**kw:records.append(execute(label,argv,cwd,out,**kw))
    run('pre-publication-identity',[sys.executable,str(ROOT/'scripts/verify_four_result_publication.py')],ROOT)
    sources={p.relative_to(ROOT).as_posix():sha(p) for p in PROJECT.rglob('*') if p.is_file() and '.lake' not in p.relative_to(PROJECT).parts and (p.suffix in ['.lean','.toml'] or p.name in ['lean-toolchain','lake-manifest.json'])}
    packages=[]
    for item in json.loads((PROJECT/'lake-manifest.json').read_text())['packages']:
        path=PROJECT/'.lake/packages'/item['name'];rev=subprocess.check_output(['git','-C',str(path),'rev-parse','HEAD'],text=True).strip()
        assert rev==item['rev'],item['name']+' revision mismatch'
        assert not subprocess.check_output(['git','-C',str(path),'status','--porcelain','--untracked-files=no'],text=True).strip(),item['name']+' dirty'
        lib=path/'.lake/build/lib/lean';assert not list(lib.glob('IsingBulk*')) and not list(lib.glob('Audit*'))
        packages.append({'name':item['name'],'revision':rev})
    binary=Path(shutil.which('lean')).resolve();toolchain=binary.parent.parent
    assert subprocess.check_output([str(binary),'--githash'],text=True).strip()=='5045d0056413266e57c625dcd7c365b10e377c52'
    commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip();tree=subprocess.check_output(['git','rev-parse','HEAD^{tree}'],cwd=ROOT,text=True).strip()
    identity={'phase':a.only,'started_utc':now(),'platform':platform.platform(),'python':sys.version,'checkout_commit':commit,'checkout_tree':tree,
      'git_status':subprocess.check_output(['git','status','--porcelain'],cwd=ROOT,text=True),'github_sha':os.getenv('GITHUB_SHA'),'pr_head_sha':os.getenv('PR_HEAD_SHA'),
      'source_sha256':sources,'packages':packages,'project_olean_count_before':0,
      'binaries':{n:{'path':str(toolchain/'bin'/n),'sha256':sha(toolchain/'bin'/n)} for n in ['lean','lake','leanchecker']},
      'lean_version':subprocess.check_output([str(binary),'--version'],text=True).strip(),
      'scripts_sha256':{p.relative_to(ROOT).as_posix():sha(p) for p in (ROOT/'scripts').glob('*.py') if 'publication' in p.name or 'joint' in p.name or 'four_result' in p.name}}
    shim=out/'toolchain';(shim/'bin').mkdir(parents=True)
    for item in toolchain.iterdir():
        if item.name!='bin':(shim/item.name).symlink_to(item,target_is_directory=item.is_dir())
    for item in (toolchain/'bin').iterdir():
        if item.name!='lean':(shim/'bin'/item.name).symlink_to(item)
    wrapper=shim/'bin/lean';wrapper.write_text('#!/usr/bin/env python3\nimport runpy\nrunpy.run_path('+repr(str(ROOT/'scripts/limit_publication_compilation.py'))+',run_name="__main__")\n');wrapper.chmod(0o755)
    slots=out/'compiler-slots';slots.mkdir()
    os.environ.update(LEAN_SYSROOT=str(shim),LAKE_OVERRIDE_LEAN='true',PUBLICATION_REAL_LEAN=str(binary),PUBLICATION_COMPILER_SLOTS=str(slots),PUBLICATION_MAX_COMPILERS=str(a.max_compilers),
      LEAN_NUM_THREADS='2',RAYON_NUM_THREADS='2',LAKE_ARTIFACT_CACHE='false',LAKE_NO_CACHE='true')
    identity['environment']={k:os.environ[k] for k in ['LEAN_SYSROOT','LAKE_OVERRIDE_LEAN','PUBLICATION_MAX_COMPILERS','LAKE_ARTIFACT_CACHE','LAKE_NO_CACHE']}
    (out/'runtime-and-source-identity.json').write_text(json.dumps(identity,indent=2)+'\n')
    prefix=['lake','-f',config];status='FAIL'
    try:
        run(a.only+'-build',prefix+['-R','-H','build',root,audit])
        actions=[json.loads(line) for line in (slots/'compiler-executions.jsonl').read_text().splitlines()]
        objects=sorted((PROJECT/'.lake/build/lib/lean').rglob('*.olean'))
        provenance=[]
        for obj in objects:
            source=PROJECT/(obj.relative_to(PROJECT/'.lake/build/lib/lean').with_suffix('.lean'))
            matches=[r for r in actions if r['output']==str(obj.resolve()) and r['exit_code']==0 and r['source_unchanged'] and r['source_sha256'].get(str(source.resolve()))==sha(source) and r['output_sha256']==sha(obj)]
            assert len(matches)==1,'Missing or duplicate genuine compiler action: '+str(obj)
            provenance.append({'source':str(source),'source_sha256':sha(source),'output':str(obj),'output_sha256':sha(obj),'compiler_action':matches[0]})
        assert objects,'No project compilation occurred'
        (out/'COMPILER_PROVENANCE.json').write_text(json.dumps({'status':'PASS','compiled_project_objects':len(objects),'objects':provenance},indent=2)+'\n')
        run(a.only+'-strict-audit',prefix+['env','lean','-j1','-DwarningAsError=true',audit+'.lean'])
        template=(ROOT/'verification/joint/PublicationClosure.lean.in').read_text()
        def closure(scan=endpoint,injection=''):
            s=template
            for key,value in {'ROOT':root,'ENDPOINT':endpoint,'SCAN_ROOT':scan,'INJECTION':injection,'REQUIRED':'#['+', '.join('`'+n for n in required)+']'}.items():s=s.replace('@'+key+'@',value)
            return s
        fixture=out/'PublicationClosure.lean';fixture.write_text(closure())
        if a.only=='joint':
            assert fixture.read_bytes()==(PROJECT/'AuditJointPublicationClosure.lean').read_bytes()
        run(a.only+'-publication-closure',prefix+['env','lean','-j1','-DwarningAsError=true',str(PROJECT/'AuditJointPublicationClosure.lean') if a.only=='joint' else str(fixture)])
        injected=out/'RejectInjectedAxiom.lean';injected.write_text(closure('publicationInjected','axiom publicationFalse : False\ntheorem publicationInjected : False := publicationFalse'))
        run(a.only+'-reject-injected-axiom',prefix+['env','lean','-j1','-DwarningAsError=true',str(injected)],expected=r'PUBLICATION unexpected axiom: publicationFalse')
        physical=out/'RejectPhysicalContract.lean'
        contracts={
          'joint':'open IsingBulk.Joint in\nexample {corrH corrL : PhysicalField.CorrelationFamily} {mH mL : PhysicalField.MagnetizationFamily} : JointFullConclusion corrH corrL mH mL := by\n  exact @full_joint_conclusion corrH corrL mH mL\n',
          'lt':'open IsingBulk.Final in\nexample (J : ℝ) (chi : ℂ → ℂ) (M : ℝ → ℂ) : True := by\n  exact @theorem_nb_physical J (by positivity) chi M\n',
          'ht':'open IsingBulk.HT.Final in\nexample (J : ℝ) (chi : ℂ → ℂ) : True := by\n  exact @publishedPhysicalSusceptibility_germ_natural_boundary J\n',
          'aniso':'open IsingBulk.Anisotropic in\nexample : True := by\n  exact @full_uniform_field_conclusion\n'}
        # A missing physical contract must fail at the actual exact application.
        body='import '+root+'\n'+contracts[a.only]
        if a.only=='lt':
            body='import '+root+'\nopen IsingBulk.Final in\nexample (J : ℝ) (hJ : 0 < J) (chi : ℂ → ℂ) (M : ℝ → ℂ) : True := by\n  exact @theorem_nb_physical J hJ chi M\n'
        physical.write_text(body)
        run(a.only+'-reject-physical-contract',prefix+['env','lean','-j1','-DwarningAsError=true',str(physical)],expected=r'Type mismatch',expected_line=len(body.splitlines()))
        if a.only=='joint':
            run('joint-frozen-controls',[sys.executable,str(ROOT/'scripts/run_joint_audit_controls.py'),'--project',str(ROOT),'--lean-root',str(PROJECT),'--output',str(out/'joint-control-evidence')])
            assert json.loads((out/'joint-control-evidence/RESULT.json').read_text())['passed']
        if a.only=='aniso':
            run('aniso-original-publication-closure',prefix+['env','lean','-j1','-DwarningAsError=true','AuditAnisotropicClosure.lean'])
            for name in ['Nonvacuity','CompleteScope','PhysicalConventions']:run('aniso-control-'+name,prefix+['env','lean','-j1','-DwarningAsError=true','IsingBulk/Anisotropic/Controls/'+name+'.lean'])
        run(a.only+'-fresh-replay',prefix+['env','leanchecker','--fresh','--verbose',root])
        assert all(sha(ROOT/p)==h for p,h in sources.items()),'Source changed during execution'
        run('post-publication-identity',[sys.executable,str(ROOT/'scripts/verify_four_result_publication.py')],ROOT)
        (out/'project-proof-object-sha256.json').write_text(json.dumps({p.relative_to(PROJECT/'.lake/build').as_posix():sha(p) for p in (PROJECT/'.lake/build').rglob('*.olean*') if p.is_file()},indent=2)+'\n')
        status='PASS'
    finally:
        (out/'SUMMARY.json').write_text(json.dumps({'status':status,'phase':a.only,'checkout_commit':commit,'checkout_tree':tree,'receipts':records,'finished_utc':now()},indent=2)+'\n')
    print('PASS: selected source-clean integrated publication gates',a.only,flush=True)
if __name__=='__main__':main()
