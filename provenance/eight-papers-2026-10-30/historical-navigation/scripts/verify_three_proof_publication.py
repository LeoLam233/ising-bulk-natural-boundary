#!/usr/bin/env python3
"""Additive three-result source, manuscript and publication identity gate."""
from pathlib import Path
import difflib,hashlib,json,os,shutil,subprocess,sys,tempfile

ROOT=Path(__file__).resolve().parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()

def verify_historical_ht_view():
    # The historical HT manifest includes the then-current repository map.
    # Preserve that version identity and execute its unchanged verifiers in a
    # temporary view, while all proof/configuration bytes come from this tree.
    manifest=json.loads((ROOT/'HT_1747_OVERLAY_MANIFEST.json').read_text(encoding='utf8'))
    paths=set(manifest['baseline_files'])|set(manifest['overlay_files'])
    paths|={'HT_1747_OVERLAY_MANIFEST.json','scripts/verify_unified_publication.py',
            'scripts/verify_ht_source_overlay.py','paper/ht/publication/manuscript.tex',
            'paper/ht/publication/EDITORIAL.json'}
    paths|={f'{phase}/{name}' for phase in ['low-temperature','high-temperature'] for name in ['README.md','README.zh.md','CITATION.cff']}
    scratch=ROOT/'.local' if os.name=='nt' else Path(tempfile.gettempdir())
    scratch.mkdir(parents=True,exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='ising-historical-ht-view-',dir=scratch) as name:
        view=Path(name)
        assert view.resolve().is_relative_to(scratch.resolve())
        for rel in paths:
            source=ROOT/rel
            if rel=='REPOSITORY_MAP.md':source=ROOT/'provenance/aniso/history/HT_20261021_REPOSITORY_MAP.md'
            dest=view/rel;dest.parent.mkdir(parents=True,exist_ok=True)
            shutil.copyfile(source,dest)
        print('Checking unchanged HT verifier in its preserved historical navigation context',flush=True)
        subprocess.run([sys.executable,str(view/'scripts/verify_unified_publication.py')],check=True)

def main():
    subprocess.run([sys.executable,str(ROOT/'scripts/verify_aniso_source_overlay.py')],check=True)
    verify_historical_ht_view()
    path=ROOT/'paper/aniso/publication'
    frozen=(ROOT/'paper/aniso/frozen/manuscript.tex').read_bytes()
    publication=(path/'manuscript.tex').read_bytes()
    marker=b'\\begin{document}'
    assert frozen.count(marker)==publication.count(marker)==1
    assert frozen[frozen.index(marker):]==publication[publication.index(marker):],'ANISO mathematical document body changed'
    record=json.loads((path/'EDITORIAL.json').read_text())
    assert record['frozen_source_sha256']==sha(frozen)=='75b94ec77e167fc4cd4b96ac44df90f6245cc20ab396ca6a4fc619d88d9c60f5'
    assert record['publication_source_sha256']==sha(publication)
    assert record['document_body_from_begin_document_sha256']==sha(frozen[frozen.index(marker):])
    assert record['document_body_byte_identical'] is True and record['mathematical_text_edits']==0
    # Every changed or added line is one of the authorized preamble directives.
    a=frozen[:frozen.index(marker)].decode().splitlines()
    b=publication[:publication.index(marker)].decode().splitlines()
    for op,i,j,k,l in difflib.SequenceMatcher(a=a,b=b).get_opcodes():
        if op=='equal':continue
        assert all(line.startswith(('\\author','\\date','\\hypersetup')) for line in a[i:j]+b[k:l]),'Non-metadata preamble change'
    assert b'pdfauthor={Dehao Lin}' in publication and b'lindh9@mail2.sysu.edu.cn' in publication
    diff=''.join(difflib.unified_diff(frozen.decode().splitlines(True),publication.decode().splitlines(True),fromfile='frozen/manuscript.tex',tofile='publication/manuscript.tex'))
    assert (path/'EDITORIAL.diff').read_text()==diff
    assert sha((path/'manuscript.pdf').read_bytes())==record['publication_pdf_sha256']
    qa=json.loads((path/'PDF_QA.json').read_text())
    assert qa['pdf_sha256']==record['publication_pdf_sha256'] and qa['compile_exit_code']==0
    assert qa['visual_review_complete'] is True and qa['unresolved_references']==0
    for phase in ['low-temperature','high-temperature','anisotropic']:
        for name in ['README.md','README.zh.md','CITATION.cff']:
            assert (ROOT/phase/name).is_file(),str(ROOT/phase/name)
    for name in ['README','PROOF_MAP','PHYSICAL_INPUTS','BUILD_AND_VERIFY','VERSION_IDENTITY','AUDIT_EVIDENCE','EDITORIAL_FOLLOWUP_SCOPE']:
        assert (ROOT/f'docs/aniso/{name}.md').is_file()
    assert (ROOT/'lean/AuditAnisotropicClosure.lean').is_file()
    assert not list((ROOT/'lean/IsingBulk/Anisotropic').rglob('*.olean'))
    print('PASS: three distinct result entrances/citations; exact frozen C001; metadata-only ANISO TeX body; compiled and reviewed publication PDF')

if __name__=='__main__':main()
