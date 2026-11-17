#!/usr/bin/env python3
"""Rebuild the eight current manuscripts without modifying published assets."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    out = parser.parse_args().output.resolve()
    papers = ROOT / 'papers'
    publication_dirs = (papers, ROOT / 'archive')
    if any(out.is_relative_to(directory) for directory in publication_dirs):
        parser.error('--output must be outside papers/ and archive/')

    sources = sorted(papers.rglob('manuscript.tex'))
    if len(sources) != 8:
        parser.error('expected eight manuscript sources under papers/')

    manifest = out / 'MANUSCRIPT_SHA256.json'
    manifest.unlink(missing_ok=True)
    results = []
    hashes = {}
    for src in sources:
        rel = src.relative_to(ROOT)
        dst = (out / src.parent.relative_to(papers)).resolve()
        if (not dst.is_relative_to(out)
                or any(dst.is_relative_to(directory) for directory in publication_dirs)):
            parser.error(f'invalid manuscript build directory: {dst}')
        dst.mkdir(parents=True, exist_ok=True)
        tex = dst / src.name
        pdf = tex.with_suffix('.pdf')
        shutil.copyfile(src, tex)
        pdf.unlink(missing_ok=True)

        for pass_number in range(1, 4):
            result = subprocess.run(
                ['pdflatex', '-no-shell-escape', '-interaction=nonstopmode',
                 '-halt-on-error', '-file-line-error', tex.name],
                cwd=dst, capture_output=True,
            )
            (dst / f'pass-{pass_number}.stdout').write_bytes(result.stdout)
            (dst / f'pass-{pass_number}.stderr').write_bytes(result.stderr)
            if result.returncode:
                print(result.stdout.decode(errors='replace'))
                print(result.stderr.decode(errors='replace'))
                raise RuntimeError(f'TeX build failed: {rel}')

        log = (dst / 'manuscript.log').read_text(encoding='utf8', errors='replace')
        problems = ('undefined references', 'undefined on input', 'multiply defined',
                    'Overfull', 'Missing character:')
        if any(problem in log for problem in problems) or not pdf.is_file():
            raise RuntimeError(f'TeX output failed validation: {rel}')

        hashes[rel.as_posix()] = sha256(tex.read_bytes()).hexdigest()
        hashes[rel.with_suffix('.pdf').as_posix()] = sha256(pdf.read_bytes()).hexdigest()
        results.append({'source': rel.as_posix(), 'result': 'BUILD_SUCCEEDED'})

    summary = json.dumps(results, indent=2)
    (out / 'BUILD_RESULTS.json').write_text(summary + '\n', encoding='utf8')
    manifest.write_text(json.dumps(hashes, indent=2, sort_keys=True) + '\n', encoding='utf8')
    print(summary)


if __name__ == '__main__':
    main()
