# HT version and evidence identities

- Frozen Lean candidate: `HT_STANDALONE_20261020T1747Z` (the **1747** source freeze).
- Mathematical manuscript: **HT-1.0**, 17 October 2026; audited source/PDF under `paper/ht/frozen/`.
- Runtime: Lean 4.34.1, compiler commit `5045d0056413266e57c625dcd7c365b10e377c52`.
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- Pre-existing LT source Git tree (unchanged): `ca47fde26285028603c7e87a9893aad31933b526`.
- HT overlay: 397 `IsingBulk.HT` modules, 35 new reusable bridge modules, `IsingBulkHT.lean`, `AuditHT.lean` and `lakefile.ht.toml`.
- Exact freeze manifest: `HT_1747_OVERLAY_MANIFEST.json` in the accompanying source integration kit. Each added proof file is copied **byte-identically** from the audited freeze, without renaming Lean modules or changing imports.

Two independent AI hostile audits (Pro/coordinated and Codex/coordinated) reported `EXHAUSTED`. Four independent Codex source-only builds, strict `AuditHT` and fresh official kernel replays completed successfully in the latter audit. Place full logs, receipts, paper-to-Lean ledgers and other large archives on the **HT version-specific GitHub Release**, with digest metadata. Do not place the ~55 MB research audit ZIP inside the tracked production source tree.

The unchanged earlier LT release `v0.2.1` retains its original historical scientific scope. LT `v0.3.0-rc2` and HT `1747` are distinct development/version identities even though their formalization sources share one repository.
