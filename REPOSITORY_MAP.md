# Three results and shared proof boundaries

| Result | Reader entrance | Mathematical manuscript | Exact Lean endpoint | Build / citation |
|---|---|---|---|---|
| Fixed-ratio anisotropic, both phases | [ANISO](anisotropic/README.md) | [Publication](paper/aniso/publication/manuscript.pdf), [frozen](paper/aniso/frozen/manuscript.pdf) | `IsingBulk.Anisotropic.full_uniform_field_conclusion` in [FullTheorem.lean](lean/IsingBulk/Anisotropic/Final/FullTheorem.lean) | [Build](docs/aniso/BUILD_AND_VERIFY.md), [citation](anisotropic/CITATION.cff) |
| Isotropic high temperature | [HT](high-temperature/README.md) | [HT-1.0 publication](paper/ht/publication/manuscript.pdf) | `IsingBulk.HT.Final.publishedPhysicalSusceptibility_germ_natural_boundary` in [PublishedPhysicalTheorem.lean](lean/IsingBulk/HT/Final/PublishedPhysicalTheorem.lean) | [Build](docs/ht/BUILD_AND_VERIFY.md), [citation](high-temperature/CITATION.cff) |
| Isotropic low temperature | [LT](low-temperature/README.md) | [v0.1-rc6](paper/next/manuscript.pdf) | `IsingBulk.Final.theorem_nb_physical` in [UnconditionalNaturalBoundary.lean](lean/IsingBulk/Final/UnconditionalNaturalBoundary.lean) | [Build](lean/README.md), [citation](low-temperature/CITATION.cff) |

## Source ownership

| Source | Role |
|---|---|
| `lean/IsingBulk/{Algebra,Analysis,First,Tail,Final}/` | Original LT development and shared foundations; existing bytes preserved |
| `lean/IsingBulk/HT/`, `lean/IsingBulk/HT.lean` | Existing HT development; existing bytes preserved |
| `lean/IsingBulk/Anisotropic/` | 762 additive frozen C001 modules |
| `lean/IsingBulk.lean`, `lean/Audit.lean`, `lean/lakefile.toml` | Existing LT root/audit/config |
| `lean/IsingBulkHT.lean`, `lean/AuditHT.lean`, `lean/lakefile.ht.toml` | Existing HT root/audit/config |
| `lean/IsingBulkAnisotropic.lean`, `lean/AuditAnisotropic.lean`, `lean/lakefile.anisotropic.toml` | Byte-identical additive C001 root/audit/config |
| `lean/AuditAnisotropicClosure.lean` | New separate publication closure audit; includes partiality checks |
| `lean/lean-toolchain`, `lean/lake-manifest.json` | One unchanged toolchain and dependency lock for all results |

No duplicate LT/HT mathematical library is created. ANISO reuses the existing normalized isotropic seeds at their actual full-sum scope. The [C001 overlay manifest](ANISO_C001_OVERLAY_MANIFEST.json) identifies 2,279 frozen files: 1,514 shared identical paths and 765 additive paths. It also binds 1,872 protected prior files. The earlier [HT overlay manifest](HT_1747_OVERLAY_MANIFEST.json) and all historical verifiers retain their identities.

## Papers, history and evidence

LT `paper/next/` and earlier `paper/` artifacts, HT `paper/ht/frozen/` and metadata-only `paper/ht/publication/` are retained. ANISO uses `paper/aniso/frozen/` (38-page audit), `paper/aniso/publication/` (author metadata only), and `paper/aniso/research-original/` (separate historical 39-page original). [Paper index](paper/README.md) · [Version index](docs/VERSIONS.md).

Historical `MANIFEST.json`, `CLAIMS.md`, `LIMITATIONS.md`, `release/next/`, earlier source snapshots and old release assets keep their version-specific scope. The root citation is a current three-result router; phase-specific citations retain independent identities. Large audit archives and fresh execution logs belong in release assets/Actions artifacts, outside Git. [ANISO provenance](docs/aniso/AUDIT_EVIDENCE.md).

The [ANISO workflow](.github/workflows/aniso-lean-acceptance.yml) and [three-result workflow](.github/workflows/three-proof-publication-acceptance.yml) are additive. Existing phase-specific LT/HT workflows are unchanged. The prior combined publication workflow retains its LT/HT jobs with current version-aware identity routing; its original bytes are archived under `provenance/aniso/history/`. The [separate editorial scope](docs/aniso/EDITORIAL_FOLLOWUP_SCOPE.md) does not edit any frozen proof text in this publication.
