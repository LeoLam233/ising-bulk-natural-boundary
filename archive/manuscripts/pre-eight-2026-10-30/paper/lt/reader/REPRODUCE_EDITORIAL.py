#!/usr/bin/env python3
"""Replay preserved editorial operations into a NEW output; does not edit the authority."""
from pathlib import Path
import argparse,json,hashlib
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('canonical',type=Path)
p.add_argument('output',type=Path)
a=p.parse_args()
if a.output.exists():raise FileExistsError(a.output)
raw=a.canonical.read_bytes()
assert hashlib.sha256(raw).hexdigest()=='44dd21ea379b66f186d3fcc322bee7b0f5497e7c1dfc54d76dfa79bd0f2720c3'
s=raw.decode('utf-8')
ops=json.loads((Path(__file__).resolve().parent/'EDITORIAL_OPERATIONS.json').read_text(encoding='utf-8'))
assert len(ops)==104
for op in ops:
    if op['old']==r'\begin{proof}' and op.get('original_line') is None:
        anchor=r'\label{'+op['section']+'}'
        assert s.count(anchor)==1,op['id']
        pos=s.index(op['old'],s.index(anchor))
    else:
        assert s.count(op['old'])==1,op['id']
        pos=s.index(op['old'])
    s=s[:pos]+op['new']+s[pos+len(op['old']):]
data=s.encode('utf-8')
assert hashlib.sha256(data).hexdigest()=='70d887dcc4912276186e852b5468f098e222eeaa4caa9232c68e037aa4e24b1c'
a.output.write_bytes(data)
print('PASS:104 operations reproduce the accepted unchanged LT Reader source.')
