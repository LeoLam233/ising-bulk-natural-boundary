# Repository organization and proof boundaries

## Mathematical proofs

| Purpose | Path | Owning proof |
|---|---|---|
| LT root and audit | `lean/IsingBulk.lean`, `lean/Audit.lean` | LT |
| LT proof development and reusable libraries | `lean/IsingBulk/{Algebra,Analysis,First,Tail,Final}/` | LT/shared |
| HT formal proof | `lean/IsingBulk/HT/` and `lean/IsingBulk/HT.lean` | HT |
| HT root and audit | `lean/IsingBulkHT.lean`, `lean/AuditHT.lean` | HT |
| HT-required reusable modules (35) | `lean/IsingBulk/First/Regular*.lean`, `lean/IsingBulk/Analysis/BranchUpper.lean` | Shared, first introduced by HT |
| LT Lake configuration | `lean/lakefile.toml` | LT; unchanged |
| HT additive Lake configuration | `lean/lakefile.ht.toml` | HT |

No copied LT source tree and no second mathlib pin. The verified frozen HT project is the existing LT tree **plus** 432 additional proof modules, two HT root/audit files and an additive Lake configuration. Moving common modules into a new namespace would change their certified source bytes; it is not part of this publication.

## Manuscripts, evidence and history

| Content | Path |
|---|---|
| LT active development manuscript | `paper/next/` (historical layout preserved) |
| LT original rc4 artifacts | `paper/` |
| LT index | `paper/lt/README.md`, `docs/lt/README.md` |
| HT frozen manuscript | `paper/ht/frozen/` |
| HT proof/citation/verification notes | `docs/ht/` |
| LT historical audit/reconstruction records | `audits/`, `research-history/`, `reproduction/`, `release/next/` |
| HT archived independent audit evidence | HT-specific GitHub Release assets (not copied into Lean modules) |

Root-level LT metadata files, including `CITATION.cff`, `CLAIMS.md` and historical manifests, still describe their established **LT version** until a separate repository-wide citation revision is prepared. Historical artifact manifests are not silently rewritten when HT is added.

## Publication gates

1. Freeze source identity and confirm the pre-existing LT Git tree is unchanged.
2. Complete author/citation/license metadata for newly published HT material.
3. Integrate the source-only HT overlay in a dedicated branch; run LT regression and HT clean build, AuditHT and fresh kernel replay on the combined checkout.
4. Merge by PR after checks, then create a clearly scoped HT release tag/assets; preserve LT tags and release identities.
