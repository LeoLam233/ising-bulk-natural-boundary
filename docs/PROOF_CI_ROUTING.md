# Publication checks and Lean acceptance

The [eight-route status](eight-papers/EIGHT_PAPER_FORMALIZATION_STATUS.md)
lists seven completed Lean routes with their exact scope. The two-complex-coupling
endpoint/transport alternative (JOINT-PSER) retains its status
`NOT_SEPARATELY_FORMALIZED`.

`.github/workflows/eight-paper-publication.yml` runs a lightweight integrity
job on pull requests to `main` and pushes to `main`. It checks the live
collection (eight TeX/PDF pairs, disclosures, and current navigation links)
and checks the frozen archive, earlier Lean sources and dependency pins
against their historical identities. Living documentation and new Lean modules
can change without changing those records. Legacy validators use a temporary
checkout of the pinned pre-migration commit.

- The manuscript job rebuilds all eight papers only when manuscript files
  under `papers/` or the build script change. Edits to Markdown and Lean
  alone do not install TeX or rebuild manuscripts.
- The F002 job runs when a pull request changes F002 sources, its build
  inputs or this workflow's proof routing. It checks the merge result. The
  ordinary push after merge checks publication integrity; it does not repeat
  the F002 proof build. Route formal changes through pull requests.
- For a broader run, use **Actions → Eight-paper publication and F002
  acceptance → Run workflow**. Dispatch runs historical validators, all eight
  manuscript builds, and the F002 proof check. The existing route-specific
  manual workflows remain available for their own releases and regressions.

CI uses the complete Git change range so an overlay with hundreds of files
does not displace manuscript changes from the build selection. To run the
editorial and historical checks locally, use a full Git checkout:

```bash
python3 scripts/verify_eight_papers.py
python3 scripts/verify_eight_papers.py --historical-checks
python3 scripts/build_current_papers.py --output PATH
```

The build writes outside the publication directories. It requires
`pdflatex`, TeX Live's extra LaTeX and recommended fonts, and Latin Modern.

## F002 proof

From `lean/`, with the pinned Lean 4.34.1 toolchain and existing lockfile:

```bash
lake exe cache get
mkdir -p ../evidence/support_c03
lake build +IsingBulk.AnisoF002.C03.FullUniformFieldConclusion \
  +IsingBulk.AnisoF002.Audit.C03FinalReplayBundle
lake env leanchecker --fresh IsingBulk.AnisoF002.C03.FullUniformFieldConclusion
```

Use a clean checkout for a fresh source build. The build uses the default Lake
configuration and the pinned upstream dependency cache. It elaborates the
terminal and the final audit bundle, including the exact signature check,
stored proof route checks, structural discovery and controls. The last command
replays the terminal module separately with the official Lean kernel. See
[F002 scope and provenance](aniso-f002/PUBLICATION.md) for the accepted theorem
and audit scope.
