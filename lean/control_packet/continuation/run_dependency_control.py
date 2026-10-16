"""A bounded adversarial control: an UNUSED E3 parameter must be detected.

This mutates only a new temporary fixture, never production sources.
"""
import argparse,json,pathlib,re,subprocess,sys,tempfile

ROOT=pathlib.Path(__file__).resolve().parents[2]
def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--lean-bin-dir',type=pathlib.Path,required=True)
    a=p.parse_args()
    sys.path.insert(0,str(ROOT/'tools/continuation'))
    from preflight import clean_environment,snapshot,reject_dependency_project_namespaces
    before=snapshot(ROOT,a.lean_bin_dir)
    source=(ROOT/'control_packet/continuation/fixtures/InternalRegularity.lean').read_text()
    extra='''theorem IsingBulkControls.counterfeit_nb
    (_unusedE3 : PublishedTWFixedOrderInput (1:ℂ)) :
    ∀ z : ℂ, ‖z‖ = 1 → ¬ HasExteriorExtension exteriorNormalizedBulk z := theorem_nb

'''
    marker='open Lean Elab Command in\nrun_cmd do'
    assert source.count(marker)==1
    source=source.replace(marker,extra+marker)
    source,count=re.subn(r'for endpoint in #\[.*?\] do',
      'for endpoint in #[`IsingBulkControls.counterfeit_nb] do',source,count=1,flags=re.S)
    assert count==1
    scratch=ROOT/'.local';scratch.mkdir(exist_ok=True)
    work=pathlib.Path(tempfile.mkdtemp(prefix='unused-e3-control-',dir=scratch))
    fixture=work/'UnusedE3.lean';fixture.write_text(source)
    argv=[str(a.lean_bin_dir/'lake'),'-f','lakefile.toml','env',str(a.lean_bin_dir/'lean'),
          '-j1','-DwarningAsError=true',str(fixture)]
    reject_dependency_project_namespaces(ROOT)
    result=subprocess.run(argv,cwd=ROOT,env=clean_environment(a.lean_bin_dir),capture_output=True,text=True,timeout=240)
    (work/'stdout.log').write_text(result.stdout);(work/'stderr.log').write_text(result.stderr)
    expected='E3 is transitively reachable from IsingBulkControls.counterfeit_nb: IsingBulk.First.PublishedTWFixedOrderInput'
    passed=result.returncode==1 and expected in result.stdout and not result.stderr
    after=snapshot(ROOT,a.lean_bin_dir)
    keys=('PROOF_CRITICAL_PAYLOAD_ID','VERIFICATION_INPUT_ID','RUNTIME_ID')
    unchanged=all(before[k]==after[k] for k in keys)
    record={'case':'unused_E3_parameter_rejected','passed':passed and unchanged,
            'exit_code':result.returncode,'expected_diagnostic':expected,'argv':argv,
            'context':{k:before[k] for k in keys},'context_unchanged':unchanged,
            'scope':'The same compiled type/body traversal must reject an unused E3 hypothesis on an otherwise valid NB wrapper.'}
    (work/'result.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps(record,indent=2))
    print('CONTROL_LOG_DIRECTORY',work)
    return 0 if record['passed'] else 1
if __name__=='__main__':raise SystemExit(main())
