"""Inventory version/premise language across current and historical source files.

This is a review aid, not an automated semantic or mathematical verdict.
Run after the mathematical validation; inspect current-context matches manually.
"""
import argparse,collections,datetime,hashlib,json,pathlib,re,subprocess

ROOT=pathlib.Path(__file__).resolve().parents[1]
PATTERN=re.compile(r'PublishedTWFixedOrderInput|\bE3\b|v0\.2\.[01]|v0\.1-rc[45]|v0\.3\.0-rc1|9,?199|14 endpoints|no Lean|no.{0,12}formaliz|not.{0,12}formaliz|\bpending\b|PARTIAL:|complete.{0,25}amplitude|unconditional.identification',re.I)
TEXT_SUFFIXES={'.md','.tex','.lean','.json','.tsv','.yml','.yaml','.toml','.cff','.py','.txt','.sh','.ps1'}

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',type=pathlib.Path,required=True);a=p.parse_args()
    assert not a.output.exists(),'Use a new receipt path'
    paths=subprocess.check_output(['git','-c','safe.directory=*','ls-files','--cached','--others','--exclude-standard','-z'],cwd=ROOT).decode().split('\0')
    protected={e['path'] for e in json.loads((ROOT/'provenance/NEXT_BASELINE.json').read_text())['protected_files']}
    predecessor=json.loads((ROOT/'provenance/AMPLITUDE_BASELINE.json').read_text())
    retained={e['path'] for e in predecessor['retained_files']}
    categories=collections.Counter();matches=[];inventory=[];text_count=0
    for name in sorted(set(paths)-{''}):
        file=ROOT/name
        if not file.is_file():continue
        category=('protected_historical' if name in protected else 'preserved_historical_copy' if name.startswith('lean/history/') else 'preserved_verified_rc5' if name in retained else 'current_candidate')
        categories[category]+=1
        data=file.read_bytes()
        inventory.append({'path':name,'category':category,'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()})
        if file.suffix not in TEXT_SUFFIXES:continue
        try:source=data.decode('utf-8')
        except UnicodeDecodeError:continue
        text_count+=1
        for line,text in enumerate(source.splitlines(),1):
            if PATTERN.search(text):matches.append({'path':name,'line':line,'category':category,'text':text})
    receipt={'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
      'scope':'All tracked and unignored candidate files, including unmodified files. Phrase matches require contextual review; generated/ignored build trees are excluded.',
      'categories':dict(categories),'text_files_scanned':text_count,'inventory':inventory,'matches':matches,
      'automatic_semantic_verdict':False}
    a.output.parent.mkdir(parents=True,exist_ok=True);a.output.write_text(json.dumps(receipt,indent=2,ensure_ascii=False)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({'files':len(inventory),'text_files':text_count,'categories':dict(categories),
      'matches':len(matches),'current_context_matches':sum(e['category']=='current_candidate' for e in matches)},indent=2))

if __name__=='__main__':main()
