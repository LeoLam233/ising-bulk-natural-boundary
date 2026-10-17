"""Build only manuscript v0.1-rc6; historical versions retain their Git identities."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

ROOT=Path(__file__).resolve().parents[1]
digest=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--pdflatex',default='pdflatex')
    a=parser.parse_args()
    source=ROOT/'paper/next/manuscript.tex'
    scratch=ROOT/'.local';scratch.mkdir(exist_ok=True)
    work=Path(tempfile.mkdtemp(prefix='rc6-paper-',dir=scratch))
    shutil.copyfile(source,work/source.name)
    commands=[]
    for n in range(1,4):
        argv=[a.pdflatex,'-interaction=nonstopmode','-halt-on-error',source.name]
        result=subprocess.run(argv,cwd=work,capture_output=True)
        (work/f'pass-{n}.stdout').write_bytes(result.stdout)
        (work/f'pass-{n}.stderr').write_bytes(result.stderr)
        commands.append({'argv':argv,'pass':n,'exit_code':result.returncode,
                         'stdout_sha256':hashlib.sha256(result.stdout).hexdigest(),
                         'stderr_sha256':hashlib.sha256(result.stderr).hexdigest()})
        if result.returncode:raise SystemExit(result.stdout.decode(errors='replace'))
    log=(work/'manuscript.log').read_text(encoding='utf-8',errors='replace')
    bad=[x for x in ('undefined references','undefined on input','multiply defined','Rerun to get','Overfull') if x in log]
    if bad:raise SystemExit('Unresolved final TeX diagnostics: '+', '.join(bad))
    aux=(work/'manuscript.aux').read_text(encoding='utf-8')
    labels=[{'label':l,'number':n,'page':int(p)} for l,n,p in
            re.findall(r'\\newlabel\{([^}]+)\}\{\{([^}]*)\}\{(\d+)\}',aux)]
    source_labels=re.findall(r'\\label\{([^}]+)\}',source.read_text(encoding='utf-8'))
    assert len(source_labels)==len(set(source_labels))
    assert set(source_labels)=={r['label'] for r in labels}
    old=json.loads((ROOT/'paper/LABEL_INDEX.json').read_text(encoding='utf-8'))
    previous=json.loads(subprocess.check_output(
        ['git','-c','safe.directory=*','show',
         'dd977048c2380e775d83b97ae1fba354c04c349a:paper/next/LABEL_INDEX.json'],cwd=ROOT,text=True))
    numbers={r['label']:r['number'] for r in labels}
    assert all(numbers[r['label']]==r['number'] for r in old),'Existing mathematical label numbering drifted'
    assert all(numbers[r['label']]==r['number'] for r in previous),'Verified rc5 label numbering drifted'
    dest=source.parent
    shutil.copyfile(work/'manuscript.pdf',dest/'manuscript.pdf')
    (dest/'LABEL_INDEX.json').write_text(json.dumps(labels,indent=2)+'\n',encoding='utf-8',newline='\n')
    version=subprocess.check_output([a.pdflatex,'--version'],text=True).splitlines()[0]
    receipt={'manuscript':'v0.1-rc6','lean_candidate':'v0.3.0-rc2','engine':version,
             'source_sha256':digest(source),'pdf_sha256':digest(dest/'manuscript.pdf'),
             'label_index_sha256':digest(dest/'LABEL_INDEX.json'),
             'label_count':len(labels),'old_labels_retaining_numbers':len(old),
             'rc5_labels_retaining_numbers':len(previous),
             'commands':commands,'log_directory':work.relative_to(ROOT).as_posix(),
             'final_tex_diagnostics':bad,'visual_qa':'Recorded separately; compilation alone is not visual QA.'}
    (dest/'BUILD.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps(receipt,indent=2))


if __name__=='__main__':main()
