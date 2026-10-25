#!/usr/bin/env python3
"""Bound real Lean compiler concurrency and record exact source/output actions."""
import fcntl,hashlib,json,os,subprocess,sys,time
from pathlib import Path
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    slots=Path(os.environ['PUBLICATION_COMPILER_SLOTS']);selected=None
    while selected is None:
        for i in range(int(os.environ['PUBLICATION_MAX_COMPILERS'])):
            f=(slots/f'slot-{i}').open('a')
            try:fcntl.flock(f,fcntl.LOCK_EX|fcntl.LOCK_NB);selected=f;break
            except BlockingIOError:f.close()
        if selected is None:time.sleep(.1)
    argv=[os.environ['PUBLICATION_REAL_LEAN'],*sys.argv[1:]]
    sources=[Path(x).resolve() for x in argv[1:] if x.endswith('.lean') and Path(x).is_file()]
    output=Path(argv[argv.index('-o')+1]).resolve() if '-o' in argv else None
    record={'argv':argv,'cwd':str(Path.cwd()),'started_unix':time.time(),
            'source_sha256':{str(p):sha(p) for p in sources},'output':str(output) if output else None}
    try:code=subprocess.call(argv)
    finally:
        record.update(finished_unix=time.time(),exit_code=locals().get('code'),
          source_unchanged=all(sha(Path(p))==h for p,h in record['source_sha256'].items()),
          output_sha256=sha(output) if output and output.is_file() else None)
        with (slots/'compiler-executions.jsonl').open('a') as log:
            fcntl.flock(log,fcntl.LOCK_EX);log.write(json.dumps(record)+'\n')
        selected.close()
    raise SystemExit(code)
if __name__=='__main__':main()
