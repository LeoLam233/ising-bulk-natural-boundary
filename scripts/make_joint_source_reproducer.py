#!/usr/bin/env python3
"""Create a source-only archive of an exact committed publication snapshot."""
import argparse,hashlib,io,json,subprocess,zipfile
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--output',required=True,type=Path);a=p.parse_args()
    target=a.output.resolve();assert not target.exists() and not target.is_relative_to(ROOT)
    commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
    raw=subprocess.check_output(['git','archive','--format=zip','HEAD'],cwd=ROOT)
    with zipfile.ZipFile(io.BytesIO(raw)) as original,zipfile.ZipFile(target,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as out:
        files={}
        for info in original.infolist():
            if info.is_dir():continue
            n=info.filename;assert '.git/' not in n and '/.lake/' not in n and not n.endswith(('.olean','.ilean')) and '.olean.' not in n
            data=original.read(info);out.writestr('repository/'+n,data);files[n]=hashlib.sha256(data).hexdigest()
        out.writestr('SNAPSHOT.json',json.dumps({'commit':commit,'files_sha256':files},indent=2)+'\n')
        out.writestr('REPRODUCIBILITY.md',f'''# JOINT C002 committed source reproducer

Commit: `{commit}`. This archive contains the full committed repository snapshot,
without Git history, toolchain binaries, dependency caches or project objects.
`SNAPSHOT.json` binds every repository member. Install Lean 4.34.1, commit
5045d0056413266e57c625dcd7c365b10e377c52, and use the unchanged Mathlib lockfile.

Initialize a local Git repository in `repository/` and commit the preserved
snapshot, then run `python3 scripts/verify_four_result_publication.py`.
From `repository/lean`, prepare upstream packages with
`lake -f lakefile.joint.toml exe cache get`. For each phase joint, lt, ht, aniso,
create a distinct new source checkout using `scripts/prepare_three_proof_checkout.py`
and execute `scripts/run_four_result_verification.py --only PHASE --output /absolute/new/receipts`.
The original publication commit remains `{commit}`; a locally initialized snapshot
will have its own Git commit identity. File identities are the reproducibility link.

Validate completed receipts using `scripts/verify_joint_execution_receipts.py`.
These are new builds and same-kernel replays, separate from validation of historical
execution records. See `repository/docs/joint/BUILD_AND_VERIFY.md` for exact gates.
''')
    print(json.dumps({'commit':commit,'path':str(target),'bytes':target.stat().st_size,'sha256':hashlib.sha256(target.read_bytes()).hexdigest()}))
if __name__=='__main__':main()
