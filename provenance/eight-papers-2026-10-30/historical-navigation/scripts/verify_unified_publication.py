"""Verify the frozen two-proof sources and the separately identified HT edition."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]

def main():
    subprocess.run([sys.executable, str(ROOT/'scripts/verify_ht_source_overlay.py')], check=True)
    frozen = (ROOT/'paper/ht/frozen/manuscript.tex').read_bytes()
    publication = (ROOT/'paper/ht/publication/manuscript.tex').read_bytes()
    record = json.loads((ROOT/'paper/ht/publication/EDITORIAL.json').read_text())
    assert hashlib.sha256(frozen).hexdigest() == record['frozen_source_sha256']
    assert hashlib.sha256(publication).hexdigest() == record['publication_source_sha256']
    assert frozen.split(b'\\begin{document}',1)[1] == publication.split(b'\\begin{document}',1)[1]
    a,b=frozen.decode().splitlines(),publication.decode().splitlines()
    changes=[(x,y) for x,y in zip(a,b) if x!=y]
    assert len(a)==len(b) and len(changes)==3
    assert all(x.startswith(('\\hypersetup','\\author','\\date')) for x,y in changes)
    assert b'pdfauthor={Dehao Lin}' in publication
    assert b'lindh9@mail2.sysu.edu.cn' in publication
    for phase in ['high-temperature','low-temperature']:
        assert (ROOT/phase/'README.md').is_file()
        assert (ROOT/phase/'README.zh.md').is_file()
        assert (ROOT/phase/'CITATION.cff').is_file()
    print('PASS: publication mathematics byte-identical; exactly three editorial preamble lines changed; two independent citations present')

if __name__ == '__main__':
    main()
