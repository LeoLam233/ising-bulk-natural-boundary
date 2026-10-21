"""Source-only HT build, strict audit and fresh replay, with complete receipts."""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import threading
import time

ROOT=Path(__file__).resolve().parents[1]
PROJECT=ROOT/'lean'

def execute(label,argv,cwd,output):
    target=output/label
    target.mkdir(parents=True,exist_ok=False)
    receipt=dict(argv=argv,cwd=str(cwd),started_utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
    (target/'command.json').write_text(json.dumps(receipt,indent=2))
    start=time.monotonic()
    proc=subprocess.Popen(argv,cwd=cwd,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    lock=threading.Lock()
    with (target/'combined.log').open('wb') as combined:
        def capture(stream,name):
            with (target/name).open('wb') as out:
                while block:=stream.read1(65536):
                    out.write(block);out.flush()
                    with lock:
                        combined.write(block);combined.flush()
                        sys.stdout.buffer.write(block);sys.stdout.buffer.flush()
        threads=[threading.Thread(target=capture,args=(proc.stdout,'stdout.log')),
                 threading.Thread(target=capture,args=(proc.stderr,'stderr.log'))]
        for thread in threads:thread.start()
        code=proc.wait()
        for thread in threads:thread.join()
    receipt.update(exit_code=code,elapsed_seconds=time.monotonic()-start,
                   finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                   logs_sha256={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in target.glob('*.log')})
    (target/'receipt.json').write_text(json.dumps(receipt,indent=2))
    if code:raise SystemExit(code)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',required=True,type=Path)
    output=parser.parse_args().output.resolve()
    output.mkdir(parents=True,exist_ok=False)
    existing=list((PROJECT/'.lake/build').rglob('*.olean')) if (PROJECT/'.lake/build').exists() else []
    assert not existing,'HT verification requires zero preexisting project .olean files'
    manifest=json.loads((ROOT/'HT_1747_OVERLAY_MANIFEST.json').read_text())
    sources={rel:hashlib.sha256((ROOT/rel).read_bytes()).hexdigest()
             for group in ['baseline_files','overlay_files'] for rel in manifest[group]}
    packages=[]
    for package in json.loads((PROJECT/'lake-manifest.json').read_text())['packages']:
        path=PROJECT/'.lake/packages'/package['name']
        actual=subprocess.check_output(['git','-C',str(path),'rev-parse','HEAD'],text=True).strip()
        assert actual==package['rev'],package['name']
        assert not subprocess.check_output(['git','-C',str(path),'status','--porcelain','--untracked-files=no'],text=True).strip()
        library=path/'.lake/build/lib/lean'
        for name in ['IsingBulk','IsingBulk.olean','IsingBulkHT.olean','Audit.olean','AuditHT.olean']:
            assert not (library/name).exists(),'Foreign project namespace in dependency cache: '+str(library/name)
        packages.append(dict(name=package['name'],revision=actual))
    binary=Path(subprocess.check_output(['which','lean'],text=True).strip()).resolve()
    identity=dict(platform=platform.platform(),python=sys.version,
        lean_version=subprocess.check_output(['lean','--version'],text=True).strip(),
        lake_version=subprocess.check_output(['lake','--version'],text=True).strip(),
        lean_launcher=str(binary),lean_launcher_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),
        github_sha=os.environ.get('GITHUB_SHA'),head_sha=os.environ.get('PR_HEAD_SHA'),
        checkout_commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
        checkout_tree=subprocess.check_output(['git','rev-parse','HEAD^{tree}'],cwd=ROOT,text=True).strip(),
        environment={k:os.environ.get(k) for k in ['LEAN_NUM_THREADS','LAKE_NO_CACHE','LAKE_ARTIFACT_CACHE']},
        project_olean_count_before=0,packages=packages,source_sha256=sources)
    (output/'runtime-and-source-identity.json').write_text(json.dumps(identity,indent=2))
    commands=[
        ('ht-build',['lake','-f','lakefile.ht.toml','-R','-H','build','IsingBulkHT','AuditHT']),
        ('ht-strict-audit',['lake','-f','lakefile.ht.toml','env','lean','-j1','-DwarningAsError=true','AuditHT.lean']),
        ('ht-fresh-replay',['lake','-f','lakefile.ht.toml','env','leanchecker','--fresh','--verbose','IsingBulkHT']),
    ]
    for label,argv in commands:execute(label,argv,PROJECT,output)
    execute('post-source-identity',[sys.executable,'scripts/verify_unified_publication.py'],ROOT,output)

if __name__=='__main__':main()
