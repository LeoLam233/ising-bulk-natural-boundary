# Reproduce LT22 Preferred22

Use the release's compact source-only bundle or a checkout of the LT22 release tag. No project proof objects, dependency cache or earlier missing Pro archive are required in the bundle. Install the exact official Linux Lean 4.34.1 runtime (release commit `5045d0056413266e57c625dcd7c365b10e377c52`) and put its `bin` directory on PATH. The nine dependency revisions in `lean/lake-manifest.json` are immutable; Mathlib is `d13f23b723b8a846827a245b89c10fc7d3f11612`. Do not run `lake update`.

From the repository root on Linux/WSL:

```sh
python3 scripts/verify_lt22_publication.py
python3 scripts/verify_lt22_preservation.py
cd lean
lake -f lakefile.toml exe cache get
cd ..
python3 -u scripts/run_lt22_acceptance.py --output /absolute/new/lt22-evidence
```

Use a new evidence destination. The runner verifies immutable source/manuscript identities and all protected files, checks actual compiler/checker binary hashes and dependency HEADs/clean tracked sources, rejects foreign project objects in dependency packages, removes only the project's `.lake/build`, and starts with zero project proof objects. It then executes:

```sh
cd lean
lake --no-cache --no-ansi -v -f lakefile.toml build IsingBulk.Preferred22
lake env leanchecker --fresh --verbose IsingBulk.Preferred22
```

Between those commands it elaborates the exact no-premise terminal type, prints its physical interfaces/axioms and walks stored types, proof values and structural support using the previously audited walker. The closure must match the audited 75,225-node graph exactly and use only `propext`, `Classical.choice`, `Quot.sound`. The stronger 75,992-node recursor-support analysis, negative controls, physical-scope audit and full dependency-cache provenance are prior immutable October 25 evidence, reused without a new adversarial audit.

Acceptance requires 486 distinct source compiler invocations, 486 distinct Built events and zero project object replays, then official fresh kernel replay with exit zero, unchanged proof objects and final source/protected-byte checks. Each command has separate stdout, stderr, UTC boundaries, exit code and stream hashes. `SUMMARY.json` is PASS only after every gate succeeds. A failed command fails the runner and CI.

The [dedicated workflow](../../.github/workflows/lt22-lean-acceptance.yml) runs on PRs, main pushes and manual dispatch and uploads complete execution evidence. A PR check does not certify different merged bytes: publication also requires success for the actual merged main SHA. Release notes bind those run URLs and the tested commit. Historical four-result acceptance is preserved through immutable files and the unchanged publication validators; any shared-source/configuration change still requires the affected old regressions under [CI routing](../PROOF_CI_ROUTING.md).

The live-tree four-result source-only validator passes directly. The older combined validator pins six navigation READMEs that main subsequently revised for Reader editions. `verify_lt22_preservation.py` therefore runs that unchanged validator in a temporary copy with only those six historical prose files restored from their exact Git bytes, following the existing HT historical-navigation-view convention. All Lean sources, configurations, manuscripts, historical manifests and validation scripts in that view come from the new repository tree. The current navigation and all other protected bytes are separately checked against the publication base. [Exact six-file record](../../provenance/lt22/HISTORICAL_NAVIGATION.json).

The source-only ZIP includes the combined repository sources, manuscripts, licenses and portable verification code, excluding `.git`, `.lake`, caches, binaries and machine-local logs. Public receipts contain commit/run identities and SHA-256 values; full machine-local historical archives stay on the author's machine.
