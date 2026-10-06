import hashlib,json,pathlib,subprocess,sys
root=pathlib.Path(__file__).resolve().parents[1]
data=json.loads((root/'ci/payload.json').read_text()); expected=data['proof_inputs']; actual=dict(expected);actual['files']={}
for name,digest in expected['files'].items():
 p=root/name
 if not p.is_file() or p.is_symlink():raise SystemExit('Missing or linked payload: '+name)
 actual['files'][name]=hashlib.sha256(p.read_bytes()).hexdigest()
 if actual['files'][name]!=digest:raise SystemExit('Payload changed: '+name)
production={p.relative_to(root).as_posix() for p in (root/'IsingBulk').rglob('*.lean')}|{'IsingBulk.lean'}
if production!={p for p in expected['files'] if p.endswith('.lean')}:raise SystemExit('Production inventory changed')
identity=hashlib.sha256(json.dumps(actual,sort_keys=True,separators=(',',':'),ensure_ascii=False).encode()).hexdigest()
if identity!=data['PROOF_CRITICAL_PAYLOAD_ID']:raise SystemExit('Identity mismatch')
if (root/'lakefile.lean').exists():raise SystemExit('Unexpected alternate Lake configuration')
if '--dependencies' in sys.argv:
 for dep in expected['dependencies']:
  path=root/'.lake/packages'/dep['name']
  revision=subprocess.check_output(['git','-C',str(path),'rev-parse','HEAD'],text=True).strip()
  if revision!=dep['revision']:raise SystemExit('Dependency revision mismatch: '+dep['name'])
print('PAYLOAD_IDENTITY_PASS',identity,'production_files',len(production))
