# Build and verify the three results

Use Lean `leanprover/lean4:v4.34.1`, compiler commit `5045d0056413266e57c625dcd7c365b10e377c52`, with the unchanged `lean/lake-manifest.json`. Mathlib is pinned to `d13f23b723b8a846827a245b89c10fc7d3f11612`; all nine exact package revisions are included in the [overlay manifest](../../ANISO_C001_OVERLAY_MANIFEST.json).

## Source and paper identities

From the repository root:

```bash
python3 scripts/verify_aniso_source_overlay.py
python3 scripts/verify_three_proof_publication.py
```

The first checks all 2,279 frozen Lean/configuration files, the 1,514 shared and 765 additive paths, and 1,872 protected prior files. When base history is available it also compares protected Git blobs with the resolved base. The second additionally runs the unchanged historical HT publication verifier in a temporary historical view: current protected proofs/configs with the archived 2026-10-21 repository map whose hash that old manifest binds. It then checks the current three-result paper hashes and complete ANISO document body, authorized preamble directives, and compiled PDF QA identity. Historical LT/HT verifiers and manifests remain unmodified; the original two-result combined workflow is archived before its current routing update.

## Clean executable gate

Begin in a new source checkout with **zero candidate-project `.olean` files**. Pinned upstream Mathlib/dependency artifacts may be reused. Fetch their official artifacts without updating the lockfile:

```bash
cd lean
lake -f lakefile.anisotropic.toml exe cache get
cd ..
python3 scripts/prepare_three_proof_checkout.py --output /absolute/new/source-checkout
python3 -u /absolute/new/source-checkout/scripts/run_three_proof_verification.py --output /absolute/new/receipt-directory
```

The preparation helper creates a fresh Git worktree and shares only `.lake/packages`. Configuration objects generated during upstream-cache preparation are left in the preparation checkout. The gate rejects every pre-existing project object, verifies dependency Git revisions and tracked cleanliness, rejects project namespaces injected into upstream caches, and records official binary hashes, compiler versions, checkout identity, source SHA-256, environment, full argv/cwd, raw stdout/stderr/combined logs, exit codes and wall-clock timings. It stops on a failed command. Re-run it from a fresh source checkout for the merged commit.

Compilation is bounded to two official Lean compiler processes through the pinned Lake release's `LEAN_SYSROOT` override and a separate `flock` execution shim; each real compiler argv is logged. Official libraries and compiler bytes are unchanged. Each compiler uses `-j1`, and the environment uses `LEAN_NUM_THREADS=2`. Candidate project outputs are never restored from a cache. `--only aniso`, `--only lt` and `--only ht` allow distinct fresh-checkout CI jobs, each with its own fresh replay; the default executes all three in sequence.

The mandatory commands executed from `lean/` are:

```bash
lake -f lakefile.anisotropic.toml -R -H build IsingBulkAnisotropic AuditAnisotropic
lake -f lakefile.anisotropic.toml env lean -j1 -DwarningAsError=true AuditAnisotropic.lean
lake -f lakefile.anisotropic.toml env leanchecker --fresh --verbose IsingBulkAnisotropic
lake -f lakefile.anisotropic.toml env lean -j1 -DwarningAsError=true AuditAnisotropicClosure.lean
lake -f lakefile.toml -R -H build IsingBulk Audit
lake -f lakefile.toml env lean -j1 -DwarningAsError=true Audit.lean
lake -f lakefile.toml env leanchecker --fresh --verbose IsingBulk
lake -f lakefile.ht.toml -R -H build IsingBulkHT AuditHT
lake -f lakefile.ht.toml env lean -j1 -DwarningAsError=true AuditHT.lean
lake -f lakefile.ht.toml env leanchecker --fresh --verbose IsingBulkHT
```

The runner also strictly executes frozen `Controls/Nonvacuity.lean`, `CompleteScope.lean` and `PhysicalConventions.lean`, then repeats the publication identity check. The unchanged original audit prints actual elaborated types and contract definitions. The new closure gate rejects partial/unsafe/sorry/unapproved-axiom dependencies of the terminal theorem and inventories the 30 project partial execution helpers outside that closure.

## GitHub Actions and receipts

[ANISO acceptance](../../.github/workflows/aniso-lean-acceptance.yml) runs the ANISO build, strict original audit, separate fresh replay, closure audit and controls. [Three-result acceptance](../../.github/workflows/three-proof-publication-acceptance.yml) runs source/manuscript identity plus the three independent build/audit/replay jobs. The existing phase-specific LT/HT workflows remain byte-identical. The prior combined publication workflow retains its proof gates with current identity/runner routing; its original bytes are archived. The combined three-result workflow runs ANISO and both regressions on PRs and merged `main`; receipts are uploaded even after failure. Upstream caches are keyed to the pinned toolchain and lockfile and never include candidate `.olean` files.

The PR and release contain the actual run URLs and compact receipts for their exact commits. Historical successful audits are provenance and are not substitutes for these executions.
