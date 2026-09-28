"""Run finite diagnostics in fresh scratch directories, never rewriting evidence.

This is not a proof checker. Thresholds below only compare historical finite
calculations; they are not certified interval error bounds.
"""
from pathlib import Path
import argparse, json, sys, os, subprocess, shutil, tempfile, time, math, re
from importlib.metadata import version

ROOT=Path(__file__).resolve().parents[1]
SKIP_METADATA={'input_files','input_hashes','input_sha256','source_sha256','environment','versions','generated_at','timestamp'}
NUMERIC=re.compile(r'^[+-]?(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?$')

def compare(a,b,path=''):
    out=[]
    if isinstance(a,dict) and isinstance(b,dict):
        ka=set(a)-SKIP_METADATA;kb=set(b)-SKIP_METADATA
        if ka!=kb:out.append(path+': key sets differ')
        for key in sorted(ka&kb):out+=compare(a[key],b[key],path+'/'+key)
    elif isinstance(a,list) and isinstance(b,list):
        if len(a)!=len(b):out.append(path+': lengths differ')
        for i,(aa,bb) in enumerate(zip(a,b)):out+=compare(aa,bb,path+'/'+str(i))
    elif isinstance(a,bool) or isinstance(b,bool):
        if a!=b:out.append(path+': boolean differs')
    elif isinstance(a,(int,float)) and isinstance(b,(int,float)):
        if not math.isclose(a,b,rel_tol=1e-10,abs_tol=1e-10):out.append(path+': numeric difference above diagnostic tolerance')
    elif isinstance(a,str) and isinstance(b,str) and NUMERIC.fullmatch(a) and NUMERIC.fullmatch(b):
        if not math.isclose(float(a),float(b),rel_tol=1e-10,abs_tol=1e-10):out.append(path+': decimal difference above diagnostic tolerance')
    elif isinstance(a,str) and isinstance(b,str) and ('j' in a or 'j' in b):
        try:
            aa,bb=complex(a),complex(b)
            if not math.isfinite(abs(aa)) or not math.isfinite(abs(bb)) or abs(aa-bb)>1e-10+1e-10*max(abs(aa),abs(bb)):
                out.append(path+': complex difference above diagnostic tolerance')
        except ValueError:
            if a!=b:out.append(path+': value differs')
    elif a!=b:out.append(path+': value differs')
    return out

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--only',nargs='+',help='Selected check IDs; default all six.')
    args=parser.parse_args()
    specs=json.loads((ROOT/'checks/SCRIPT_ORIGINS.json').read_text(encoding='utf-8'))
    if args.only:
        unknown=set(args.only)-{s['id'] for s in specs}
        if unknown:parser.error('Unknown check IDs: '+', '.join(sorted(unknown)))
        specs=[s for s in specs if s['id'] in args.only]
    scratch=ROOT/'.local';scratch.mkdir(exist_ok=True)
    run=Path(tempfile.mkdtemp(prefix='checks-',dir=scratch))
    env=os.environ.copy();env['PYTHONDONTWRITEBYTECODE']='1';env['PYTHONIOENCODING']='utf-8'
    results=[]
    for spec in specs:
        work=run/spec['id'];work.mkdir()
        script=work/Path(spec['script']).name;shutil.copyfile(ROOT/spec['script'],script)
        started=time.perf_counter()
        try:
            p=subprocess.run([sys.executable,'-B',str(script),*spec['arguments']],cwd=work,env=env,capture_output=True,timeout=600)
        except subprocess.TimeoutExpired:
            results.append({'id':spec['id'],'exit_code':None,'status':'TIMEOUT'});continue
        (work/'stdout.txt').write_bytes(p.stdout);(work/'stderr.txt').write_bytes(p.stderr)
        output=work/spec['output_file'];differences=[]
        if not output.is_file():differences=['Expected output missing']
        else:
            actual=output.read_text(encoding='utf-8-sig');expected=(ROOT/spec['expected']).read_text(encoding='utf-8-sig')
            try:
                if spec['comparison_kind']=='json':differences=compare(json.loads(actual),json.loads(expected))
                elif actual.replace('\r\n','\n').strip()!=expected.replace('\r\n','\n').strip():differences=['Text differs from historical receiver rerun']
            except (ValueError,TypeError) as exc:differences=[str(exc)]
        item={'id':spec['id'],'exit_code':p.returncode,'seconds':round(time.perf_counter()-started,3),'output':output.relative_to(ROOT).as_posix(),'historical_differences':differences,'status':'REPRODUCED_FINITE_CHECK' if p.returncode==0 and not differences else 'REVIEW_DIFFERENCE'}
        results.append(item);print(json.dumps(item),flush=True)
    record={'purpose':'Selected finite diagnostic replay; not mathematical certification','python':sys.version.split()[0],'dependencies':{x:version(x) for x in ('numpy','sympy','mpmath')},'comparison':{'numeric_rtol':1e-10,'numeric_atol':1e-10,'metadata_keys_ignored':sorted(SKIP_METADATA),'interval_certified':False},'checks':results,'all_reproduced':all(x['status']=='REPRODUCED_FINITE_CHECK' for x in results),'full_natural_boundary_certified':False}
    (run/'REPRODUCTION_RECORD.json').write_text(json.dumps(record,indent=2)+'\n',encoding='utf-8')
    print('Record: '+(run/'REPRODUCTION_RECORD.json').relative_to(ROOT).as_posix())
    return 0 if record['all_reproduced'] else 1
if __name__=='__main__':sys.exit(main())
