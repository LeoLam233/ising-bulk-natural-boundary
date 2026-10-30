# Source and manuscript identities

The outer handoff is `ANISO_C001_GITHUB_HANDOFF_20261024.zip`. Its verifier was executed before integration, followed by the inner archive's `VERIFY_INPUT.py`. The authoritative proof bytes are `project/lean/` in `ANISO_C001_INDEPENDENT_LEAN_AUDIT_INPUT_20261023.zip`, whose SHA-256 is `0fd8e6d5e47df58c662f78a6855402aebe2e5fdd89343d63cb81cbe960317d6c`.

The historical C001 label `d825684173015b4d8c77faa217bdb5aef2b6a5fb` is **not an independently reconstructed Git commit**: the original candidate's Git object database was not supplied. Per-file SHA-256 establishes the frozen identity. The starting and resolved repository base is `76c3ad5457e883cc15032fdf4205da23ceba58fe`; current `main` agreed when fetched for integration.

## Exact overlay

| Set | Count | Treatment |
|---|---:|---|
| Frozen Lean source | 2,274 | Every supplied byte retained |
| Frozen configuration/toolchain/lock files | 5 | Every supplied byte retained |
| Shared frozen LT/HT paths | 1,514 | Compared byte for byte; no overwrite |
| Additive frozen paths | 765 | 762 ANISO modules, `IsingBulkAnisotropic.lean`, `AuditAnisotropic.lean`, `lakefile.anisotropic.toml` |
| Protected pre-existing repository files | 1,872 | No modification or deletion; includes old proofs/configs/papers/manifests/workflows |

The [overlay manifest](../../ANISO_C001_OVERLAY_MANIFEST.json) lists every path and hash. [SOURCE_IDENTITY.json](../../provenance/aniso/SOURCE_IDENTITY.json) preserves the original handoff identity. The new closure audit and publication scripts are separately authored additions. Existing LT/HT proof trees, configs, dependency lock, toolchain, earlier verifiers and historical release records retain their bytes and identities.

## Manuscripts

| Artifact | SHA-256 |
|---|---|
| Frozen 38-page PDF | `bda31a0f9e84a5b500ddf34f06d11ddf9fece41dfa24c5be50c0f562c98b3f75` |
| Frozen TeX | `75b94ec77e167fc4cd4b96ac44df90f6245cc20ab396ca6a4fc619d88d9c60f5` |
| Publication 38-page PDF | `86f0d81715b76cf78be011eb4b302ce920ad5251611513094f11521c42c27c6f` |
| Publication TeX | `d5c38eb5666291b8af02ff4e30fc4f7d50e932034bcbb29ad734990623a5fc24` |
| Identical body including `\begin{document}` | `d46a55cd75bed2fa3d455624fbaa53b858d22cd1730255a64d95b16d47626224` |
| Separate 39-page research-original PDF | `9252c8d43fc489396fa9fe822d26aa6257e3ed82c95cdcf55f1158246320de85` |
| Separate research-original TeX | `2596c367f17132d7b5e6fb0619f4bb965031d16c3bfddcc66b02c44aaa526c2c` |

The [editorial JSON](../../archive/manuscripts/pre-eight-2026-10-30/paper/aniso/publication/EDITORIAL.json), [literal diff](../../archive/manuscripts/pre-eight-2026-10-30/paper/aniso/publication/EDITORIAL.diff), [edition explanation](../../archive/manuscripts/pre-eight-2026-10-30/paper/aniso/publication/README.md) and [PDF QA](../../archive/manuscripts/pre-eight-2026-10-30/paper/aniso/publication/PDF_QA.json) describe the metadata-only derivation. The historical original is never substituted for the audited edition.

LT `archive/manuscripts/pre-eight-2026-10-30/paper/next/`, HT `archive/manuscripts/pre-eight-2026-10-30/paper/ht/frozen/` and HT's 21 October 2026 publication edition remain intact. The [global version index](../VERSIONS.md) preserves the historical LT ledger verbatim below the current result index.
