"""Prepare deterministic public assets after the exact full CI has passed."""
import argparse,gzip,hashlib,io,json,pathlib,shutil,subprocess,tarfile
p=argparse.ArgumentParser();p.add_argument('--state',type=pathlib.Path,required=True);p.add_argument('--commit',required=True);p.add_argument('--tree',required=True);p.add_argument('--run',required=True);a=p.parse_args()
root=pathlib.Path.cwd();out=a.state/'assets';out.mkdir(exist_ok=False)
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def archive(dest,files):
 with dest.open('xb') as raw,gzip.GzipFile(filename='',mode='wb',fileobj=raw,mtime=0) as gz,tarfile.open(fileobj=gz,mode='w') as tar:
  for name,path in sorted(files):
   data=path.read_bytes();info=tarfile.TarInfo(name);info.size=len(data);info.mode=0o644;info.mtime=0;tar.addfile(info,io.BytesIO(data))
tracked=subprocess.check_output(['git','ls-files','-z'],text=True).split('\0')
source=[(x,root/x) for x in tracked if x and (x.startswith('lean/') or x.startswith('.github/workflows/')) and not x.startswith('lean/release-inputs/')]
archive(out/'Ising_v0.2.0_Lean_Source.tar.gz',source)
expected=json.loads((root/'lean/release-inputs/EVIDENCE_BINDING.json').read_text())
evidence=a.state/'Ising_v0.2.0_Internal_Evidence.tar.gz'
with evidence.open('xb') as stream:
 for part in expected['parts']:
  member=root/'lean/release-inputs'/part['name']
  assert member.stat().st_size==part['bytes'] and sha(member)==part['sha256']
  stream.write(member.read_bytes())
assert evidence.stat().st_size==expected['bytes'] and sha(evidence)==expected['sha256']
shutil.copyfile(evidence,out/evidence.name)
ci=a.state/'full-ci';results=list(ci.rglob('sequence.result.json'));assert len(results)==1,'Ambiguous full CI sequence receipt'
r=json.loads(results[0].read_text());identity=json.loads((root/'lean/ci/accepted_identity.json').read_text())
assert r['status']=='CHECK_SEQUENCE_PASSED_NOT_AUDIT_ROUND' and r['fresh_kernel_replay_exit']==0
assert all(r[k]==v for k,v in identity.items())
assert len(r['stages'])==5 and all(s['exit_code']==0 for s in r['stages'])
assert r['production_module_count']==1071 and r['endpoint_count']==12 and r['audited_safe_declaration_count']==9199
archive(out/'Ising_v0.2.0_Full_Remote_CI.tar.gz',[(str(x.relative_to(ci)),x) for x in ci.rglob('*') if x.is_file()])
shutil.copyfile(root/'paper/manuscript.pdf',out/'Ising_v0.2.0_Manuscript.pdf')
assets=[{'name':x.name,'bytes':x.stat().st_size,'sha256':sha(x)} for x in sorted(out.iterdir())]
manifest={'version':'v0.2.0','commit':a.commit,'tree':a.tree,'full_ci_run_id':int(a.run),'proof_payload_id':identity['PROOF_CRITICAL_PAYLOAD_ID'],'verification_id':identity['VERIFICATION_INPUT_ID'],'assets':assets,'scope':'Manifest lists payload assets; SHA256SUMS additionally lists this manifest. The remote verification receipt records every uploaded asset, including both index files.'}
(out/'Ising_v0.2.0_Asset_Manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
(out/'SHA256SUMS.txt').write_text(''.join(sha(x)+'  '+x.name+'\n' for x in sorted(out.iterdir())))
print(json.dumps({'assets':len(list(out.iterdir())),'directory':str(out)}))
