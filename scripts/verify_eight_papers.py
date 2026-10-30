#!/usr/bin/env python3
"""Verify current editions, exact whole-tree archive and protected base bytes."""
from pathlib import Path
import argparse,hashlib,json,re,subprocess,sys
ROOT=Path(__file__).resolve().parents[1]
BASE='923266754afd65f5922a51f59a72ca56e1a88942'
PREFIX='archive/manuscripts/pre-eight-2026-10-30/'
RECORD='provenance/eight-papers-2026-10-30/MIGRATION.json'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def git(*args):return subprocess.check_output(['git','-c','safe.directory='+ROOT.as_posix(),'-C',str(ROOT),*args])
def base_entries():
 out={}
 for line in git('ls-tree','-r',BASE).decode().splitlines():
  mode,kind,rest=line.split(' ',2);blob,path=rest.split('\t',1);out[path]=blob
 return out
def verify():
 m=json.loads((ROOT/RECORD).read_text(encoding='utf8'));assert m['base']==BASE
 old=base_entries();assert len(old)==4009
 actual_lean={p.relative_to(ROOT).as_posix() for p in (ROOT/'lean').rglob('*') if p.is_file() and not any(x in p.relative_to(ROOT/'lean').parts for x in ['.lake','.local','__pycache__'])}
 assert actual_lean=={n for n in old if n.startswith('lean/')},('Added/missing formal-tree files',sorted(actual_lean^{n for n in old if n.startswith('lean/')}))
 allowed=m['navigation_and_routing_changes']
 for rel,row in allowed.items():
  assert not rel.startswith(('lean/','verification/','provenance/','release/','audits/','research-history/'))
  assert rel.startswith(('.github/workflows/','scripts/','docs/','low-temperature/','high-temperature/','anisotropic/','joint/')) or rel in ['README.md','README.zh.md','REPOSITORY_MAP.md','AUTHORSHIP.md']
  assert digest(ROOT/rel)==row['new_sha256'],('Changed navigation/routing bytes',rel)
  prev=ROOT/m['historical_navigation_prefix']/rel
  assert digest(prev)==row['old_sha256'],('Historical routing bytes',rel)
  raw=prev.read_bytes();assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==old[rel]
  if rel.startswith('scripts/'):
   now=(ROOT/rel).read_text(encoding='utf8');before=prev.read_text(encoding='utf8')
   addition=row['routing_insertion'];assert now.replace(addition,'',1)==before,('Historical validator core edited',rel)
 count=0;protected=0
 for rel,wanted in old.items():
  if rel in allowed:continue
  p=ROOT/(PREFIX+rel if rel.startswith('paper/') else rel)
  assert p.is_file() and not p.is_symlink(),('Missing/linked protected file',rel)
  raw=p.read_bytes();got=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
  assert got==wanted,('Protected byte identity changed',rel)
  count+=rel.startswith('paper/');protected+=not rel.startswith('paper/')
 assert count==67 and not (ROOT/'paper').exists()
 actual={p.relative_to(ROOT).as_posix() for p in (ROOT/PREFIX/'paper').rglob('*') if p.is_file()}
 assert actual=={PREFIX+n for n in old if n.startswith('paper/')}
 current={p.relative_to(ROOT).as_posix() for p in (ROOT/'papers').rglob('*') if p.suffix in ['.tex','.pdf']}
 assert current==set(m['current_pairs']) and len(current)==16
 for rel,row in m['current_pairs'].items():
  assert digest(ROOT/rel)==row['sha256'],('Current candidate changed',rel)
  if rel.endswith('.tex'):
   s=(ROOT/rel).read_text(encoding='utf8');assert s.count('ChatGPT')==1 and 'Dehao Lin' in s
 # All live Markdown files outside sealed historical material have resolvable relative links.
 bad=[]
 for rel in m['live_markdown']:
  p=ROOT/rel;s=p.read_text(encoding='utf8')
  for target in re.findall(r'!?\[[^\]]*\]\(([^)]+)\)',s):
   target=target.strip().split(' "',1)[0].split('#',1)[0]
   if not target or re.match(r'^[a-zA-Z][a-zA-Z0-9+.-]*:',target):continue
   target=target.replace('%20',' ')
   if not (p.parent/target).resolve().exists():bad.append((rel,target))
 assert not bad,('Broken active links',bad)
 print(json.dumps({'status':'PASS','base':BASE,'archived_files':count,'other_protected_files':protected,'unchanged_lean_files':sum(n.startswith('lean/') for n in old),'current_tex_pdf_files':16,'navigation_routing_files':len(allowed),'formal_recompilation':'not required for byte-identical formal sources'},indent=2))
 return m
def main():
 p=argparse.ArgumentParser();p.add_argument('--historical-checks',action='store_true');p.add_argument('--ci-mode',action='store_true');a=p.parse_args()
 verify()
 if a.historical_checks:
  from eight_paper_paths import historical_root
  v=historical_root(ROOT,already_verified=True)
  subprocess.run([sys.executable,str(v/'scripts/verify_ht22_preservation.py')],cwd=v,check=True)
 if a.ci_mode:
  # Reuse prior accepted formal artifacts only after every protected source byte passed above.
  print('formal=false')
if __name__=='__main__':main()
