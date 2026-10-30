#!/usr/bin/env python3
"""Verify the byte-identical HT 1747 source overlay and unmodified LT basis."""
from pathlib import Path
import hashlib,json,sys
base=Path(__file__).resolve().parents[1]
# Editorial migration: preserve the historical checker core in a verified temporary view.
from eight_paper_paths import historical_root
base=historical_root(base)

manifest=json.loads((base/'HT_1747_OVERLAY_MANIFEST.json').read_text(encoding='utf8'))
for key in ['baseline_files','overlay_files']:
    for rel,expected in manifest[key].items():
        path=base/rel
        if not path.is_file():
            raise SystemExit('Missing '+rel)
        digest=hashlib.sha256(path.read_bytes()).hexdigest()
        if digest != expected:
            raise SystemExit('Source mismatch '+rel)
print('PASS: '+str(len(manifest['baseline_files']))+' unchanged LT files; '
      +str(len(manifest['overlay_files']))+' exact HT publication overlay files')
