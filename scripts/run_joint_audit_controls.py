#!/usr/bin/env python3
"""Small author controls, never independent-audit or fresh-replay credit."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

ERROR = re.compile(r'^(.+?\.lean):(\d+):(\d+): error(?:\([^)]*\))?: (.*)$', re.M)
INFRA = re.compile(r'unknown (module|constant|identifier|tactic)|invalid import|'
                   r'no such file|failed to load|out of memory|heartbeats|'
                   r'timeout|stack overflow|interrupted|killed|unexpected token', re.I)

def classify(name, lines, pattern, code, stdout, stderr):
    errors = ERROR.findall(stdout+'\n'+stderr)
    if INFRA.search(stdout+'\n'+stderr) or stderr:
        return False
    if pattern is None:
        return code == 0 and not errors and 'JOINT_STRICT_LOGICAL_CLOSURE_PASS:' in stdout
    return code == 1 and bool(errors) and all(
        Path(path).name == name and int(line) in lines and re.search(pattern, message)
        for path, line, column, message in errors)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--lean-root',type=Path,help='Separate built immutable Lean worktree')
    a = parser.parse_args()
    root = a.project.resolve()
    lean_root = a.lean_root.resolve() if a.lean_root else root/'lean'
    out = a.output.resolve()
    out.mkdir(parents=True,exist_ok=False)
    cases = [
        ('AcceptSafeClosure',None),
        ('AcceptOpaquePartialWrapper',None),
        ('RejectInjectedAxiom',r'JOINT unapproved endpoint axiom:'),
        ('RejectReachablePartial',r'\(kernel\) invalid declaration, safe declaration must not contain partial declaration'),
        ('RejectMissingMechanism',r'JOINT required mathematical mechanism absent from actual closure:'),
        ('RejectSorry',r'declaration uses `sorry`'),
        ('RejectMissingPhysicalInputs',r'Type mismatch'),
        ('RejectMissingFamilyScope',r'Type mismatch'),
        ('RejectMissingOnsiteSubtraction',r'Type mismatch'),
        ('RejectMissingBeta',r'Type mismatch'),
        ('RejectSwappedPhases',r'Type mismatch'),
        ('RejectVacuousComplexDomain',r'Type mismatch')]
    records = []
    for stem, pattern in cases:
        fixture = root/'verification/joint/control_fixtures'/(stem+'.lean')
        source = fixture.read_text()
        lines = [i+2 for i,line in enumerate(source.splitlines()) if 'EXPECT_FAILURE_HERE' in line]
        command = ['lake','-f','lakefile.joint.toml','env','lean','-j1','-DwarningAsError=true',str(fixture)]
        start = time.monotonic()
        result = subprocess.run(command,cwd=lean_root,text=True,capture_output=True,check=False)
        (out/(stem+'.stdout.log')).write_text(result.stdout)
        (out/(stem+'.stderr.log')).write_text(result.stderr)
        records.append({'name':stem,'command':command,'exit_code':result.returncode,
            'wall_seconds':time.monotonic()-start,'source_sha256':hashlib.sha256(fixture.read_bytes()).hexdigest(),
            'expected_error_lines':lines,'expected_pattern':pattern,
            'passed':classify(fixture.name,lines,pattern,result.returncode,result.stdout,result.stderr)})
    # A diagnostic at the wrong location, an infrastructure error, a signal,
    # and unexpected acceptance can never masquerade as expected rejection.
    diagnostic = 'T.lean:3:0: error: intended\n'
    checks = [classify('T.lean',[3],'intended',1,diagnostic,''),
              not classify('T.lean',[4],'intended',1,diagnostic,''),
              not classify('Other.lean',[3],'intended',1,diagnostic,''),
              not classify('T.lean',[3],'intended',1,diagnostic+'unknown module X',''),
              not classify('T.lean',[3],'intended',-9,diagnostic,''),
              not classify('T.lean',[3],'intended',0,'','')]
    summary = {'passed':all(r['passed'] for r in records) and all(checks),
               'cases':records,'classifier_controls':checks,
               'independent_audits':0,'fresh_kernel_replay':False}
    (out/'RESULT.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))
    return 0 if summary['passed'] else 1

if __name__ == '__main__':
    raise SystemExit(main())
