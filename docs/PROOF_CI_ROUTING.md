# Local publication checks and Lean replay

The [eight-route status](eight-papers/EIGHT_PAPER_FORMALIZATION_STATUS.md)
lists the Lean results and scope for each manuscript.

GitHub Actions is disabled for this repository. The files under
`.github/workflows/` record the previous CI configuration.

## Publication checks

From the root of a full Git checkout, run the publication verifier or rebuild
the manuscripts locally.

```bash
python3 scripts/verify_eight_papers.py
python3 scripts/build_current_papers.py --output PATH
```

The verifier checks the current manuscript paths, disclosures and navigation
links, as well as the frozen archive, earlier Lean sources and dependency pins.
Add `--historical-checks` to run the legacy validators in a temporary checkout
of the pinned pre-migration commit.

The build writes outside the publication directories. It requires
`pdflatex`, TeX Live's extra LaTeX and recommended fonts, and Latin Modern.

## F002 proof

From `lean/`, with the pinned Lean 4.34.1 toolchain and existing lockfile:

```bash
lake -f lakefile.aniso-f002-continuation.toml exe cache get
mkdir -p ../evidence/support_c03
lake -f lakefile.aniso-f002-continuation.toml build \
  +IsingBulk.AnisoF002.C03.FullUniformFieldConclusion \
  +IsingBulk.AnisoF002.Audit.C03FinalReplayBundle
lake -f lakefile.aniso-f002-continuation.toml env leanchecker --fresh \
  IsingBulk.AnisoF002.C03.FullUniformFieldConclusion
```

Use a clean checkout for a fresh source build. The frozen continuation Lake
configuration registers a support library imported by the final audit. The
explicit module arguments select the terminal and final audit bundle. The
build uses the pinned upstream dependency cache and runs the signature check,
stored proof route checks, structural discovery and controls. The last command
replays the terminal module separately with the official Lean kernel. See
[F002 scope and provenance](aniso-f002/PUBLICATION.md) for the accepted theorem
and audit scope.
