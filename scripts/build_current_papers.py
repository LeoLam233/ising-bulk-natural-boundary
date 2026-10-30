#!/usr/bin/env python3
"""Rebuild the eight current manuscripts without modifying published assets."""
from pathlib import Path
import argparse,json,shutil,subprocess
ROOT=Path(__file__).resolve().parents[1]
def main():
 p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args();out=a.output.resolve()
 assert not out.is_relative_to(ROOT/'papers') and not out.is_relative_to(ROOT/'archive')
 results=[]
 for src in sorted((ROOT/'papers').rglob('manuscript.tex')):
  dst=out/src.parent.relative_to(ROOT/'papers');dst.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst/src.name)
  for i in range(3):
   r=subprocess.run(['pdflatex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error','-file-line-error','manuscript.tex'],cwd=dst,capture_output=True)
   (dst/('pass-'+str(i+1)+'.stdout')).write_bytes(r.stdout);assert r.returncode==0,src
  log=(dst/'manuscript.log').read_text(errors='replace')
  assert not any(x in log for x in ['undefined references','undefined on input','multiply defined','Overfull','Missing character:']),src
  results.append({'source':src.relative_to(ROOT).as_posix(),'result':'BUILD_SUCCEEDED'})
 assert len(results)==8
 (out/'BUILD_RESULTS.json').write_text(json.dumps(results,indent=2)+'\n');print(json.dumps(results,indent=2))
if __name__=='__main__':main()
