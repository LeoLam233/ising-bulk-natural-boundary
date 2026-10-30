#!/usr/bin/env python3
"""Check exact frozen C002 overlay, prior identities and metadata-only edition."""
from pathlib import Path
import argparse,difflib,hashlib,json,re,subprocess,sys
ROOT=Path(__file__).resolve().parents[1]
# Editorial migration: preserve the historical checker core in a verified temporary view.
from eight_paper_paths import historical_root
ROOT=historical_root(ROOT)

sha=lambda b:hashlib.sha256(b).hexdigest()
def main():
    p=argparse.ArgumentParser();p.add_argument('--source-only',action='store_true');a=p.parse_args()
    m=json.loads((ROOT/'JOINT_C002_OVERLAY_MANIFEST.json').read_text())
    protected=m['protected_lean_paths'];added=m['additive_frozen_lean_paths']
    sm=(ROOT/'provenance/joint/frozen/SOURCE_MANIFEST.json').read_bytes()
    assert sha(sm)==m['source_manifest_sha256']=='7acb3a1472c4e9303b12357f30bfad2df0a916c3d26584c1a172a578446a869b'
    assert len(protected)==2279 and len(added)==439 and not (set(protected)&set(added))
    assert {**protected,**added}==json.loads(sm)
    joint={n for n in added if n.startswith('IsingBulk/Joint/') and n.endswith('.lean')}
    assert len(joint)==435 and set(added)-joint=={'IsingBulkJoint.lean','AuditJoint.lean','JointAudit.lean','lakefile.joint.toml'}
    for rel,h in {**protected,**added}.items():assert sha((ROOT/'lean'/rel).read_bytes())==h,rel
    assert {p.relative_to(ROOT/'lean').as_posix() for p in (ROOT/'lean/IsingBulk/Joint').rglob('*.lean')}==joint
    assert sha((ROOT/'provenance/joint/frozen/ARTIFACT_MANIFEST.json').read_bytes())=='81e3e5da224254ebbe3a899cb8ead5f1d73162c44fb9f087c19ee5327380c256'
    assert sha((ROOT/'provenance/joint/frozen/BASELINE_SHA256SUMS.txt').read_bytes())=='c63feaafa004a2701f3b600f043b935b33c3dc755401fbb3a3e99674f3365a36'
    print('PASS: 2,279 protected paths and exactly 439 frozen C002 additions (435 modules + 4 roots/audit/config)')
    if a.source_only:return
    subprocess.run([sys.executable,str(ROOT/'scripts/verify_three_proof_publication.py')],check=True)
    path=ROOT/'paper/joint/publication'
    f=(ROOT/'paper/joint/frozen/manuscript.tex').read_bytes();v=(path/'manuscript.tex').read_bytes();marker=b'\\begin{document}'
    assert sha(f)=='4d4567b2620799e187a9441d321b66079d8635600cb76f503d72fd31cf01e76e'
    assert sha((ROOT/'paper/joint/frozen/manuscript.pdf').read_bytes())=='868c0eda262821292f860fa75662afd8f3bc13b215a9e8aadee735ba7dfc4eb7'
    assert f.count(marker)==v.count(marker)==1 and f[f.index(marker):]==v[v.index(marker):]
    x=f[:f.index(marker)].decode().splitlines();y=v[:v.index(marker)].decode().splitlines()
    for op,i,j,k,l in difflib.SequenceMatcher(a=x,b=y).get_opcodes():
        if op!='equal':assert all(line.startswith(('\\author','\\date','\\hypersetup')) for line in x[i:j]+y[k:l]),'Non-metadata preamble edit'
    record=json.loads((path/'EDITORIAL.json').read_text());qa=json.loads((path/'PDF_QA.json').read_text())
    assert record['frozen_source_sha256']==sha(f) and record['publication_source_sha256']==sha(v)
    assert record['document_body_from_begin_document_sha256']==sha(f[f.index(marker):])
    assert record['document_body_byte_identical'] is True and record['mathematical_text_edits']==0
    assert record['publication_pdf_sha256']==qa['pdf_sha256']==sha((path/'manuscript.pdf').read_bytes())
    assert qa['compile_exit_codes']==[0,0] and qa['unresolved_references']==0 and qa['visual_review_complete'] is True
    assert qa['frozen_pages']==59 and len(qa['visually_reviewed_pages'])==qa['publication_pages']
    assert b'pdfauthor={Dehao Lin}' in v and b'lindh9@mail2.sysu.edu.cn' in v
    diff=''.join(difflib.unified_diff(f.decode().splitlines(True),v.decode().splitlines(True),fromfile='frozen/manuscript.tex',tofile='publication/manuscript.tex'))
    assert (path/'EDITORIAL.diff').read_text()==diff
    for phase in ['joint','anisotropic','high-temperature','low-temperature']:
        for name in ['README.md','README.zh.md','CITATION.cff']:assert (ROOT/phase/name).is_file()
    for name in ['README','PROOF_MAP','PHYSICAL_INPUTS','BUILD_AND_VERIFY','VERSION_IDENTITY','AUDIT_EVIDENCE']:assert (ROOT/f'docs/joint/{name}.md').is_file()
    print('PASS: all four result entrances; prior identities; frozen 59-page authority; exact metadata-only body; compiled/reviewed publication edition')
if __name__=='__main__':main()
