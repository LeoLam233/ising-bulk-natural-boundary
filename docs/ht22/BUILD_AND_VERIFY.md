# HT22 — build and verify

Use Ubuntu 24.04, Python 3.12+, and official Lean `leanprover/lean4:v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`. The workflow checks the official Linux archive SHA-256 `47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4` and the three executable identities. Mathlib is `d13f23b723b8a846827a245b89c10fc7d3f11612`; all nine Lake revisions remain unchanged. Never run `lake update`.

From a clean checkout with the official runtime on PATH:

```sh
python3 scripts/verify_ht22_publication.py
python3 scripts/verify_ht22_preservation.py
cd lean
lake -f lakefile.ht22.toml exe cache get
cd ..
python3 -u scripts/run_ht22_acceptance.py --output /absolute/new/ht22-evidence
```

The runner verifies/copies exact source and only pinned upstream caches into a new scratch tree. It starts with no project objects and separately executes strict root, audit and all 378 HT22 source builds with `-j1 -DwarningAsError=true`. It records actual compiler coverage for the full local closure, including otherwise unimported additions. Then it executes a separate official `lake -f lakefile.ht22.toml env leanchecker --fresh --verbose IsingBulkHT22` and rehashes source and proof objects.

Complete scanners cover actual theorem/opaque values, types, mutual inductives, every constructor, family-owned/nested recursors and rules, and quotient primitives. CI reconstructs all fourteen constructor proof arguments and their inferred types as bounded kernel-expression DAGs. Only `propext`, `Classical.choice`, `Quot.sound` are allowed. Required mechanisms must occur on stored-value/structural paths excluding type edges. Effective controls include kernel-valid old-endpoint bypass followed by required policy rejection, and hidden opaque/constructor/nested-recursion controls. The original protected scanner remains unchanged alongside the enhanced scanner.

The dedicated workflow runs on PRs, merged main and manual dispatch, with 360 minutes for the substantial clean build. Original LT/HT/ANISO/JOINT/LT22 sources, pins and manuscripts are checked by exact bytes and unchanged historical validators; temporary historical navigation views never replace published files. Old roots have no imports of the additive namespace.

The source-only release ZIP includes the complete imported local closure, all additive modules and pinned configs, with `REPRODUCE.md` and internal SHA-256 sums. Its verifier/runner use `--source-bundle` to distinguish standalone reproduction from whole-repository preservation. Exact commands, exits, raw streams, source/object identities, fourteen field records and full graphs are retained as CI artifacts. The merged-main CI URL and commit are bound into the release receipt.
