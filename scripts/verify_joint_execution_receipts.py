#!/usr/bin/env python3
"""Validate retained execution evidence; this does not rerun the Lean kernel."""
import argparse,hashlib,json
from pathlib import Path
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('directories',nargs='+',type=Path);a=p.parse_args()
    for root in a.directories:
        summary=json.loads((root/'SUMMARY.json').read_text());assert summary['status']=='PASS'
        identity=json.loads((root/'runtime-and-source-identity.json').read_text())
        assert summary['checkout_commit']==identity['checkout_commit'] and summary['checkout_tree']==identity['checkout_tree']
        assert json.loads((root/'CLEAN_SOURCE_PREFLIGHT.json').read_text())['project_olean_count_before']==0
        labels={r['label'] for r in summary['receipts']};phase=summary['phase']
        for name in ['build','strict-audit','publication-closure','reject-injected-axiom','reject-physical-contract','fresh-replay']:assert phase+'-'+name in labels,name
        for receipt in summary['receipts']:
            folder=root/receipt['label'];stored=json.loads((folder/'receipt.json').read_text());assert stored==receipt
            command=json.loads((folder/'command.json').read_text())
            for key,value in command.items():assert receipt[key]==value
            assert receipt['passed'] and receipt['elapsed_seconds']>0 and receipt['exit_code']==receipt['expected_exit']
            for name,h in receipt['logs_sha256'].items():assert sha(folder/name)==h
        provenance=json.loads((root/'COMPILER_PROVENANCE.json').read_text());assert provenance['status']=='PASS'
        expected={'joint':2555,'lt':1076,'ht':1436,'aniso':2184}[phase]
        assert provenance['compiled_project_objects']>=expected and len(provenance['objects'])==provenance['compiled_project_objects']
        actions=[json.loads(s) for s in (root/'compiler-slots/compiler-executions.jsonl').read_text().splitlines()]
        objects=json.loads((root/'project-proof-object-sha256.json').read_text())
        for item in provenance['objects']:
            r=item['compiler_action'];assert r in actions and r['exit_code']==0 and r['source_unchanged']
            assert r['source_sha256'][item['source']]==item['source_sha256']
            assert r['output']==item['output'] and r['output_sha256']==item['output_sha256']
            assert objects[item['output'].split('/.lake/build/',1)[1]]==item['output_sha256']
        if phase=='joint':assert json.loads((root/'joint-control-evidence/RESULT.json').read_text())['passed']
        print(f"PASS: {phase} {summary['checkout_commit']}; {len(summary['receipts'])} actual gates; {len(provenance['objects'])} compiler actions; raw log hashes")
if __name__=='__main__':main()
