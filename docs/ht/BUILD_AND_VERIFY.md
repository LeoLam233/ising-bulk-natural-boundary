# HT build and kernel replay

Run from `lean/` using Lean **4.34.1**, official build commit `5045d0056413266e57c625dcd7c365b10e377c52`, with the nine dependency revisions pinned in `lake-manifest.json` (Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`). The existing LT `lakefile.toml` is unchanged; HT extends it only by providing `lakefile.ht.toml` with an additional library and audit target.

```sh
cd lean
lake -f lakefile.ht.toml exe cache get
lake -f lakefile.ht.toml -R -H build IsingBulkHT AuditHT
lake -f lakefile.ht.toml env lean -j1 -DwarningAsError=true AuditHT.lean
lake -f lakefile.ht.toml env leanchecker --fresh --verbose IsingBulkHT
```

For an independent verification, start from a source-only checkout with no project `.olean` or `.lake/build` contents. Official pinned dependency caches may be reused. Preserve command lines, exit codes, original stdout/stderr, toolchain and dependency identities. Then check LT separately:

```sh
lake -f lakefile.toml build IsingBulk Audit
```

HT source provenance: `HT_STANDALONE_20261020T1747Z`; the frozen project and later AI audit logs are held as release evidence, not transiently mixed with production Lean files. The official `leanchecker --fresh` uses Lean's own kernel with an empty replay environment.
