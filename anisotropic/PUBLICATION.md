# ANISO C001 publication record

This publication integrates the supplied frozen C001 source into the existing LT/HT repository. The resolved base is `76c3ad5457e883cc15032fdf4205da23ceba58fe`. All 1,514 shared frozen paths have identical bytes; only 765 frozen paths are added. The [overlay manifest](../ANISO_C001_OVERLAY_MANIFEST.json) also protects 1,872 pre-existing files, including every prior mathematical Lean file, LT/HT configuration, frozen manuscript and historical manifest.

The planned release identity is `anisotropic-v1.0.0-leanc001`. A release is issued only after the PR's mandatory source, build, strict-audit, fresh-replay, regression and manuscript gates pass, followed by verification of the merged commit. Exact executions and final publication status are linked from the PR and release receipts; historical audit receipts do not establish acceptance of a new commit.

## Publication contents

- [Frozen 38-page mathematical audit PDF](../paper/aniso/frozen/manuscript.pdf) and exact TeX.
- [Author-identified 38-page publication PDF](../paper/aniso/publication/manuscript.pdf), with a byte-identical TeX document body.
- [Separate 39-page research-original edition](../paper/aniso/research-original/manuscript.pdf).
- Unchanged C001 proofs, [actual final theorem](../lean/IsingBulk/Anisotropic/Final/FullTheorem.lean), separate [partial/unsafe closure audit](../lean/AuditAnisotropicClosure.lean), and [reproduction instructions](../docs/aniso/BUILD_AND_VERIFY.md).
- Release manuscripts, source-only reproducer, independently checkable SHA-256 manifest, and compact execution/source receipts. Large raw logs and compiled artifacts remain outside Git.

The independent Codex archive is expected to be exactly 428,305,070 bytes with SHA-256 `5c1ef7f28e70228cc33376d5fe62e2310e93e38acce438515635561a2f506c6e`. It is attached only if those actual bytes are recovered and verified. [Evidence availability](../docs/aniso/AUDIT_EVIDENCE.md) distinguishes that archive from the missing distinct Pro archive and from newly executed publication gates.

## Editorial boundary

This PR changes only the ANISO publication preamble's author, date and PDF metadata. It preserves the complete TeX body, all frozen mathematical source, and existing LT/HT reader paths. [The follow-up scope](../docs/aniso/EDITORIAL_FOLLOWUP_SCOPE.md) reserves prose editing of three new reader editions for a separate documentation PR.
