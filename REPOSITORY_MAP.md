# Research results, manuscripts and Lean correspondence

First-time readers should open the **reviewed Reader editions** below. The original/frozen mathematical authority and the terminal Lean theorem interface remain distinct.

| Result | Complete Reader edition | Governing mathematical original | Formal theorem |
|---|---|---|---|
| Joint natural boundaries with two independent complex couplings | [PDF](paper/joint/reader/manuscript.pdf) · [TeX](paper/joint/reader/manuscript.tex) | [Frozen 59-page manuscript](paper/joint/frozen/manuscript.pdf) | [Exact theorem source](lean/IsingBulk/Joint/Final/FullConclusion.lean) |
| Fixed-ratio anisotropic natural boundaries | [PDF](paper/aniso/reader/manuscript.pdf) · [TeX](paper/aniso/reader/manuscript.tex) | [Frozen 38-page manuscript](paper/aniso/frozen/manuscript.pdf) | [Exact theorem source](lean/IsingBulk/Anisotropic/Final/FullTheorem.lean) |
| Isotropic high-temperature bulk susceptibility | [PDF](paper/ht/reader/manuscript.pdf) · [TeX](paper/ht/reader/manuscript.tex) | [Frozen original manuscript](paper/ht/frozen/manuscript.pdf) | [Exact theorem source](lean/IsingBulk/HT/Final/PublishedPhysicalTheorem.lean) |
| Isotropic low-temperature connected bulk susceptibility | [PDF](paper/lt/reader/manuscript.pdf) · [TeX](paper/lt/reader/manuscript.tex) | [Canonical v0.1-rc6 manuscript](paper/next/manuscript.pdf) | [Exact theorem source](lean/IsingBulk/Final/UnconditionalNaturalBoundary.lean) |

Reader manuscripts are editorial editions, not newly reconstructed mathematical proofs. For physical-premise and manuscript-only scope boundaries consult the result-specific proof maps and [paper index](paper/README.md).

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
| `lean/IsingBulk/Joint/`, `IsingBulkJoint.lean`, `AuditJoint.lean`, `JointAudit.lean`, `lakefile.joint.toml` | Exactly 439 byte-identical C002 additions |
| `lean/AuditJointPublicationClosure.lean` | Separate publication-only closure verifier |
| `lean/lean-toolchain`, `lean/lake-manifest.json` | One unchanged toolchain and dependency lock for all results |

No duplicate LT/HT mathematical library is created. ANISO reuses the existing normalized isotropic seeds at their actual full-sum scope. The [C001 overlay manifest](ANISO_C001_OVERLAY_MANIFEST.json) identifies 2,279 frozen files: 1,514 shared identical paths and 765 additive paths. It also binds 1,872 protected prior files. The earlier [HT overlay manifest](HT_1747_OVERLAY_MANIFEST.json) and all historical verifiers retain their identities.

## Papers, history and evidence

The reviewed Reader editions under `paper/{lt,ht,aniso,joint}/reader/` are the recommended reading entrances. LT `paper/next/` and earlier `paper/` artifacts, HT `paper/ht/frozen/` and metadata-only `paper/ht/publication/` remain retained. ANISO uses `paper/aniso/frozen/` (38-page audit), `paper/aniso/publication/` (author metadata only), and `paper/aniso/research-original/` (separate historical 39-page original). [Paper index](paper/README.md) · [Version index](docs/VERSIONS.md).

Historical `MANIFEST.json`, `CLAIMS.md`, `LIMITATIONS.md`, `release/next/`, earlier source snapshots and old release assets keep their version-specific scope. The root citation is a current four-result router; phase-specific citations retain independent identities. Large audit archives and fresh execution logs belong in release assets/Actions artifacts, outside Git. [ANISO provenance](docs/aniso/AUDIT_EVIDENCE.md).

The [ANISO workflow](.github/workflows/aniso-lean-acceptance.yml) and [three-result workflow](.github/workflows/three-proof-publication-acceptance.yml) are additive. Existing phase-specific LT/HT workflows are unchanged. The prior full LT/HT verification gate remains manually callable under the [scope-aware CI policy](docs/PROOF_CI_ROUTING.md); its original bytes are archived under `provenance/aniso/history/`. The [separate editorial scope](docs/aniso/EDITORIAL_FOLLOWUP_SCOPE.md) does not edit any frozen proof text in this publication.

The [JOINT acceptance](.github/workflows/joint-lean-acceptance.yml) and [four-result workflow](.github/workflows/four-result-publication-acceptance.yml) add exact source/manuscript checks and four independent clean builds, strict closures, negative controls and fresh replays. [JOINT provenance](docs/joint/AUDIT_EVIDENCE.md) distinguishes its separate audit archives and current publication receipts.
