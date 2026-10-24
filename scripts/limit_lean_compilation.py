#!/usr/bin/env python3
"""Linux execution shim: at most two official compiler processes, no source edits."""
import fcntl,json,os,subprocess,sys,time
from pathlib import Path

def main():
    directory=Path(os.environ['ANISO_COMPILER_SLOTS'])
    count=int(os.environ['ANISO_MAX_COMPILERS'])
    selected=None
    while selected is None:
        for i in range(count):
            slot=(directory/f'slot-{i}').open('a')
            try:
                fcntl.flock(slot,fcntl.LOCK_EX|fcntl.LOCK_NB)
                selected=slot
                break
            except BlockingIOError:slot.close()
        if selected is None:time.sleep(0.1)
    argv=[os.environ['ANISO_REAL_LEAN'],*sys.argv[1:]]
    start=time.time()
    try:code=subprocess.call(argv)
    finally:
        with (directory/'compiler-executions.jsonl').open('a') as log:
            fcntl.flock(log,fcntl.LOCK_EX)
            log.write(json.dumps(dict(argv=argv,started_unix=start,finished_unix=time.time(),exit_code=locals().get('code'))) + '\n')
        selected.close()
    raise SystemExit(code)

if __name__=='__main__':main()
