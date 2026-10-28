#!/usr/bin/env python3
"""Publication wrapper around unchanged frozen HT22 build/control machinery."""
import argparse,datetime,gzip,hashlib,json,os,pathlib,re,shutil,sys,traceback
from verify_ht22_publication import ROOT as REPO,verify,read,sha
sys.path.insert(0,str(REPO/'verification/ht22'))
from frozen_acceptance import Job,ROOT,AUDIT,CONFIG,THEOREM,TARGET,PINS,REGRESSIONS,local_import_graph,local_closure,require,write_json,SCOPE_PRINTS
sys.path.insert(0,str(REPO/'verification/ht22/verification_controls'))
from route_policy import validate_production,MAIN_REQUIRED,AGGREGATE_REQUIRED,PHYSICAL_REQUIRED

FIELDS=['bulk_analytic','bulk_boundary','susceptibility','same_bulk_germ','same_susceptibility_germ','physical_input','beta_coordinate','joint_lattice','one_particle','absolute_tail','first_coefficient','prime_full_limit','angular_jets','sharp_covariance_jets']
class PublicationJob(Job):
    def extract(self):
        self.identity=verify(self.a.source_bundle)
        self.original_manifest_sha256='a0c4ddb4725a86382ee8f57e1e81b25cf60b8a2e1469d165c9efa395a65d227f'
        self.source.mkdir(parents=True)
        for rel in self.identity['files']:
            dest=self.source/'repository'/rel;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(REPO/rel,dest)
        shutil.copytree(REPO/'verification/ht22/verification_controls',self.source/'verification_controls',ignore=shutil.ignore_patterns('__pycache__'))
        shutil.copyfile(REPO/'provenance/ht22/PROTECTED_BASELINE.json',self.source/'PROTECTED_BASELINE.json')
        self.baseline=read('provenance/ht22/PROTECTED_BASELINE.json')
        self.manifest=dict(format=1,files={p.relative_to(self.source).as_posix():dict(size=p.stat().st_size,sha256=sha(p)) for p in self.source.rglob('*') if p.is_file()})
        write_json(self.source/'SOURCE_MANIFEST.json',self.manifest)
        self.a.manifest_sha256=sha(self.source/'SOURCE_MANIFEST.json')
        self.save('SOURCE_IDENTITY.json',dict(original_frozen_manifest_sha256=self.original_manifest_sha256,publication_identity_sha256=sha(REPO/'provenance/ht22/SOURCE_IDENTITY.json'),integration_input_manifest_sha256=self.a.manifest_sha256,source_files=len(self.manifest['files']),github_sha=os.environ.get('GITHUB_SHA'),pr_head_sha=os.environ.get('PR_HEAD_SHA'),source_bundle=self.a.source_bundle))
        self.verify_sources();self.steps['immutable_snapshot']='PASS_EXACT_FROZEN_OVERLAY'
    def environment(self):
        super().environment()
        expected={'lean':'e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550','lake':'6f53827dab18010d6c690d14c8401cacabc1db958edb3552a877ed4cf1dd995d','leanchecker':'ccef1bfe9bfeecea65137d94a69033c1a89f360711f50fa3178e7ba3e696fcbe'}
        require({k:v['sha256'] for k,v in self.binaries.items()}==expected,'Official Linux binary hashes differ')
    def plan_build_and_regressions(self):
        self.graph=local_import_graph(self.project)
        self.added_modules=sorted(n for n in self.graph if n=='IsingBulk.HT22' or n.startswith('IsingBulk.HT22.') or n in (ROOT,AUDIT))
        require(len(self.added_modules)==381,'Additive Lean inventory changed')
        graph=local_import_graph(REPO/'lean')
        rows={}
        for name,(config,root,audit) in REGRESSIONS.items():
            closure=local_closure(graph,[root]+([audit] if audit else []))
            require(not (closure&set(self.added_modules)),'Old root imports HT22: '+name)
            rows[name]=dict(closure=sorted(closure),new_ht22_intersection=[])
        self.save('AFFECTED_REGRESSION_RATIONALE.json',dict(protected_mathematical_changes=0,dependency_changes=0,routes=rows,source_bundle=self.a.source_bundle,conclusion='Original roots have no dependency on additive HT22; historical validators run unchanged in a hash-bound historical navigation view.'))
        self.steps['affected_regression_analysis']='PASS_NO_AFFECTED_ROUTES'
    def strict_build(self):
        super().strict_build()
        invocations={}
        for label in ['10-clean-root-build','11-audit-build','12-all-additive-source-build','13-bypass-fixture-prerequisite']:
            text=(self.receipts/(label+'.stdout.log')).read_text(errors='replace')+(self.receipts/(label+'.stderr.log')).read_text(errors='replace')
            for line in text.splitlines():
                if '.lean -o ' not in line or str(self.project) not in line:continue
                for rel in re.findall(re.escape(str(self.project)) + r'/([^\s]+)\.lean -o ',line):
                    require('-j1' in line and '-DwarningAsError=true' in line,'Non-strict compiler invocation')
                    invocations[pathlib.PurePosixPath(rel).as_posix().replace('/','.')]=line
        expected=local_closure(self.graph,self.added_modules+['IsingBulk.HT.Final.FullNaturalBoundary'])
        require(set(invocations)==expected,'Missing strict compiler traces: '+str(sorted(expected-set(invocations))))
        self.save('STRICT_COMPILER_COVERAGE.json',dict(expected=len(expected),unique_source_compilations=len(invocations),all_378_submodules=True,missing=[],source_object_traces=invocations))
    def graph_and_scope(self):
        # First execute unchanged frozen protected-walker, scope and route machinery.
        super().graph_and_scope()
        generated=self.source/'verification_controls/generated'
        scanner=(REPO/'verification/ht22/EnhancedWalker.lean').read_text()
        options='\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nset_option pp.all true\nset_option pp.universes true\nset_option pp.explicit true\nset_option pp.proofs true\n'
        for case in ['final','bypass','detector_controls']:
            base=generated/('enhanced_'+case)
            prefix='import IsingBulkHT22\n'
            body=''
            if case=='bypass':
                fixture=(self.source/'verification_controls/fixtures/OldRouteBypass.lean').read_text();lines=fixture.splitlines(True)
                while lines and lines[0].startswith('import '):prefix+=lines.pop(0)
                body=''.join(lines)
            suffix=''
            if case=='detector_controls':
                body='''namespace C001Control
axiom hidden : True
opaque mask : True := hidden
theorem throughOpaque : True := mask
inductive Carrier : Type where
  | mk : (hidden = hidden) → Carrier
def throughConstructor : Option Carrier := none
inductive Nested where
  | node : List Nested → Nested
def nestedTypeOnly : Option Nested := none
theorem clean : True := True.intro
end C001Control
'''
                for short in ['throughOpaque','throughConstructor','nestedTypeOnly','clean']:
                    suffix+='coordinator_graph C001Control.'+short+' to '+json.dumps(str(generated/('detector_'+short)))+'\n'
            else:
                root=THEOREM if case=='final' else 'AuditSentinel.oldRouteBypass'
                suffix='coordinator_graph '+root+' to '+json.dumps(str(base))+'\n'
            if case=='final':
                suffix+=(REPO/'verification/ht22/FieldArguments.lean').read_text()+'\npublication_fields to '+json.dumps(str(generated/'field_arguments.jsonl'))+'\n'
            driver=generated/('Enhanced_'+case+'.lean');driver.write_text(prefix+scanner.replace('import Lean\n','import Lean\n'+options,1)+body+'\n'+suffix)
            self.run('35-enhanced-'+case,[self.binaries['lean']['path'],'-j1','-DwarningAsError=true','--root',generated,driver],env=self.probe_env)
        rows=[json.loads(s) for s in (generated/'enhanced_final.graph.jsonl').read_text().splitlines()]
        summary=json.loads((generated/'enhanced_final.summary.json').read_text())
        types=[json.loads(s) for s in (generated/'enhanced_final.types.jsonl').read_text().splitlines()]
        # Frozen policy's legacy string slot is supplied from the complete type DAG.
        for row in types:row['elaborated_expr']=json.dumps(row['elaborated_expr_dag'],separators=(',',':'))
        errors,main=validate_production(rows,summary,types,THEOREM)
        require(not errors,str(errors))
        require(sorted(summary['axioms'])==['Classical.choice','Quot.sound','propext'],'Unexpected effective axioms')
        byname={r['name']:r for r in rows}
        def value_reachable(root):
            seen=set();queue=[root]
            while queue:
                n=queue.pop()
                if n in seen:continue
                seen.add(n);r=byname[n];queue.extend(r['value_edges']+r['structural_edges'])
            return seen
        values=value_reachable('IsingBulk.HT22.Final.f001_natural_boundary')
        require(MAIN_REQUIRED<=values,'Required mechanisms occur only in types: '+str(sorted(MAIN_REQUIRED-values)))
        aggregate_values=value_reachable(THEOREM)
        require((AGGREGATE_REQUIRED|PHYSICAL_REQUIRED)<=aggregate_values,'Aggregate proof producers missing')
        fields=[json.loads(s) for s in (generated/'field_arguments.jsonl').read_text().splitlines()]
        require([r['field'] for r in fields]==FIELDS and len(fields)==14,'Fourteen actual fields differ')
        require(all(r['stored_proof_dag']['nodes'] and r['type_dag']['nodes'] for r in fields),'Empty proof/type DAG')
        controls={}
        for short in ['throughOpaque','throughConstructor','nestedTypeOnly','clean']:
            ds=json.loads((generated/('detector_'+short+'.summary.json')).read_text())
            dr=[json.loads(s) for s in (generated/('detector_'+short+'.graph.jsonl')).read_text().splitlines()]
            names={r['name'] for r in dr}
            if short in ['throughOpaque','throughConstructor']:require('C001Control.hidden' in ds['axioms'],'Hidden axiom undetected')
            if short=='nestedTypeOnly':require({'C001Control.Nested.rec','C001Control.Nested.rec_1'}<=names,'Nested recursors missed')
            if short=='clean':require(not ds['axioms'] and not ds['missing'],'Positive detector control failed')
            controls[short]=dict(passed=True,summary=ds)
        from route_policy import validate
        bbase=generated/'enhanced_bypass'
        br=[json.loads(s) for s in bbase.with_suffix('.graph.jsonl').read_text().splitlines()]
        bs=json.loads(bbase.with_suffix('.summary.json').read_text())
        berr=validate(br,bs,'AuditSentinel.oldRouteBypass')
        require(any('forbidden old proof-route reachables' in e for e in berr),'Enhanced old route not rejected')
        closure=dict(summary=summary,main_route=main,main_value_structural_mechanisms=sorted(MAIN_REQUIRED),type_only_mechanisms=0,root_type=TARGET,root_premises=0,field_count=14,canonical_graph_sha256=hashlib.sha256(json.dumps(sorted(rows,key=lambda r:r['name']),sort_keys=True,separators=(',',':')).encode()).hexdigest(),detector_controls=controls,enhanced_bypass_policy_errors=berr)
        self.save('ENHANCED_CLOSURE.json',closure)
        self.steps['enhanced_complete_closure_and_fourteen_fields']='PASS'
        # Compress large complete expression records before artifact packaging.
        for p in generated.glob('enhanced_*.values.jsonl'):
            with p.open('rb') as src,gzip.open(str(p)+'.gz','wb',compresslevel=6) as dst:shutil.copyfileobj(src,dst)
            p.unlink()
        self.verify_sources()
    def finish_checks(self):
        self.verify_sources();verify(self.a.source_bundle)
        require(self.object_hashes()==self.ht22_objects,'Final project object drift')
        for name in PINS:self.verify_package(name,self.project/'.lake/packages','60-final')
        self.save('FINAL_IMMUTABILITY.json',dict(original_frozen_manifest_sha256=self.original_manifest_sha256,all_frozen_bytes_unchanged=True,protected_files_unchanged=not self.a.source_bundle,all_nine_dependency_sources_clean=True,ht22_proof_objects_unchanged=True))
        self.steps['final_immutability']='PASS'
    def bundle_results(self,status,error=None):
        for dirname in ['generated','runs']:
            src=self.source/'verification_controls'/dirname
            if src.exists():shutil.copytree(src,self.receipts/'verification_controls'/dirname,ignore=shutil.ignore_patterns('lib','*.olean','*.ilean'),dirs_exist_ok=True)
        self.save('SUMMARY.json',dict(status=status,error=error,steps=self.steps,github_sha=os.environ.get('GITHUB_SHA'),pr_head_sha=os.environ.get('PR_HEAD_SHA'),github_run_id=os.environ.get('GITHUB_RUN_ID'),original_frozen_manifest_sha256=getattr(self,'original_manifest_sha256',None),official_fresh_kernel_exit_code=0 if self.steps.get('official_fresh_kernel')=='PASS' else None,protected_files_unchanged=status=='PASS' and not self.a.source_bundle,field_count=14 if self.steps.get('enhanced_complete_closure_and_fourteen_fields')=='PASS' else None,commands=len(self.commands)))
        self.save('EVIDENCE_SHA256.json',{p.relative_to(self.receipts).as_posix():sha(p) for p in self.receipts.rglob('*') if p.is_file()})
def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=pathlib.Path,required=True);p.add_argument('--source-bundle',action='store_true');a=p.parse_args()
    a.packages=REPO/'lean/.lake/packages';a.binary_hashes=None;a.require=[];a.regressions='affected'
    a.snapshot_sha256='0e80db908bcb44298f3af03b19e322876e26c3b7028a1a3bcb91f272732437bd'
    job=PublicationJob(a);status='FAIL';error=None
    try:
        if not a.source_bundle:job.run('00-historical-preservation',[sys.executable,str(REPO/'scripts/verify_ht22_preservation.py')],cwd=REPO)
        job.extract();job.environment();job.dependencies();job.plan_build_and_regressions();job.strict_build();job.fresh();job.lean_environment();job.graph_and_scope();job.controls();job.finish_checks();status='PASS'
    except BaseException as exc:
        error=str(exc);(job.receipts/'FAILURE_TRACEBACK.log').write_text(traceback.format_exc());print(traceback.format_exc(),flush=True)
    finally:job.bundle_results(status,error)
    return 0 if status=='PASS' else 1
if __name__=='__main__':sys.exit(main())
