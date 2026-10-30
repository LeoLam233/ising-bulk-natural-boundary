[Current eight-paper collection](../papers/README.md) · [Exact formalization status](eight-papers/EIGHT_PAPER_FORMALIZATION_STATUS.md).

The records below retain their version-specific historical scope. Current editions are under papers/; older article links resolve to the archive.

# Authoritative versions and artifact identities

## HT22 PSER F001 — 28 October 2026

The distinct independent high-temperature route has the exact fourteen-field root `IsingBulk.HT22.ht22_full_target : IsingBulk.HT22.HT22FullTarget`. The 378 frozen HT22 submodules, roots/audit/config, exact 22-page PDF/TeX and separate editorial clarifications retain canonical source manifest `a0c4ddb4725a86382ee8f57e1e81b25cf60b8a2e1469d165c9efa395a65d227f`. [Identity](../provenance/ht22/SOURCE_IDENTITY.json) · [Build and verify](ht22/BUILD_AND_VERIFY.md) · [versioned release](https://github.com/LeoLam233/ising-bulk-natural-boundary/releases/tag/ht22-pser-f001-v1.0.0). Earlier chronological notes below describe their original scope.


The **LT22 PSER proof** is an independent low-temperature route: [frozen 22-page PDF](../archive/manuscripts/pre-eight-2026-10-30/paper/lt/pser/manuscript.pdf) · [TeX](../archive/manuscripts/pre-eight-2026-10-30/paper/lt/pser/manuscript.tex) · [Preferred22 theorem](../lean/IsingBulk/Preferred22/FullTheorem.lean) · [scope and correspondence](../docs/lt22/PROOF_MAP.md) · [reproduce](../docs/lt22/BUILD_AND_VERIFY.md).

| Low-temperature edition | Paper | Formal route |
|---|---|---|
| Original paper (canonical LT) | [PDF](../archive/manuscripts/pre-eight-2026-10-30/paper/next/manuscript.pdf) · [TeX](../archive/manuscripts/pre-eight-2026-10-30/paper/next/manuscript.tex) | [Original LT Lean](../lean/IsingBulk/Final/UnconditionalNaturalBoundary.lean) |
| Reader paper (editorial edition of Original) | [PDF](../archive/manuscripts/pre-eight-2026-10-30/paper/lt/reader/manuscript.pdf) · [TeX](../archive/manuscripts/pre-eight-2026-10-30/paper/lt/reader/manuscript.tex) | [Original LT Lean](../lean/IsingBulk/Final/UnconditionalNaturalBoundary.lean) |
| PSER paper (LT22, distinct proof) | [22-page PDF](../archive/manuscripts/pre-eight-2026-10-30/paper/lt/pser/manuscript.pdf) · [TeX](../archive/manuscripts/pre-eight-2026-10-30/paper/lt/pser/manuscript.tex) | [Independent Preferred22 Lean](../lean/IsingBulk/Preferred22/FullTheorem.lean) |

LT22 preserves the October 25 audited source bytes: 333 new modules, 153 identical inherited modules, unchanged Lean 4.34.1 and nine dependency pins. The exact root is `IsingBulk.Preferred22.preferred_full_target : IsingBulk.Preferred22.PreferredFullTarget`, with zero root premises; Yang and Palmer–Tracy inputs are antecedents only within the physical identification clause. [Identity and prior audit](../provenance/lt22/PRIOR_ACCEPTANCE.json) · [LT22 citation](../low-temperature/lt22/CITATION.cff). The records below retain their historical version-specific scope. HT22, ANISO F002 and JOINT F001 are separate future publication tasks; this LT22 addition makes no completion or publication claim for them.

## Current publication: four result identities

JOINT C002 adds the independent two-complex-coupling parent, all finite positive-ratio descendants and complete isotropic descendants. [Frozen 59-page authority](../archive/manuscripts/pre-eight-2026-10-30/paper/joint/frozen/manuscript.pdf) · [metadata-only publication](../archive/manuscripts/pre-eight-2026-10-30/paper/joint/publication/manuscript.pdf) · [source identity](joint/VERSION_IDENTITY.md) · [citation](../joint/CITATION.cff). Release tag: `joint-v1.0.0-leanc002`; actual merge and execution identities are bound by the release receipts.

The earlier three-result identities and the historical LT ledger are retained below.

| Result | Mathematical manuscript | Lean identity | Citation |
|---|---|---|---|
| Fixed-ratio anisotropic, HT and connected plus-phase LT, all lattice sites and infinite odd/even orders | [Frozen 38-page audit](../archive/manuscripts/pre-eight-2026-10-30/paper/aniso/frozen/manuscript.pdf), [author-metadata publication](../archive/manuscripts/pre-eight-2026-10-30/paper/aniso/publication/README.md), 24 October 2026; [separate 39-page research-original](../archive/manuscripts/pre-eight-2026-10-30/paper/aniso/research-original/manuscript.pdf) | C001 file-hash identity; historical label `d825684173015b4d8c77faa217bdb5aef2b6a5fb` is not a reconstructed Git commit | [ANISO](../anisotropic/CITATION.cff) |
| High-temperature phase, complete disordered susceptibility, all odd orders | HT-1.0; [publication edition](../archive/manuscripts/pre-eight-2026-10-30/paper/ht/publication/README.md), 21 October 2026; [frozen audited edition](../archive/manuscripts/pre-eight-2026-10-30/paper/ht/frozen/manuscript.pdf) unchanged | `HT_STANDALONE_20261020T1747Z`; release `high-temperature-v1.0.0-lean1747` | [High-temperature](../high-temperature/CITATION.cff) |
| Low-temperature phase, connected ordered pure-phase susceptibility, all even orders | v0.1-rc6 | v0.3.0-rc2; original sources unchanged | [Low-temperature](../low-temperature/CITATION.cff) |

ANISO adds 765 frozen paths alongside the unmodified LT/HT sources. Its [version identity](aniso/VERSION_IDENTITY.md) binds all 2,279 frozen Lean/configuration files and both original manuscript editions. New execution receipts govern the integrated and merged commits.

The high-temperature integration record follows. The high-temperature tag identifies a separate result. It does not rename or
reassign the low-temperature releases. The baseline `lean/IsingBulk` Git tree at
integration is `ca47fde26285028603c7e87a9893aad31933b526`. All 1,079 baseline files
and 447 overlay files are bound by the [overlay manifest](../HT_1747_OVERLAY_MANIFEST.json).
The complete original standalone project has 1,521 matching production files.

The historical low-temperature version ledger follows verbatim. Statements such
as "No release tag or main merge" describe the candidate at the time of that record.
The phase-specific publication records govern the later unified publication.

## Historical low-temperature ledger

| Version / artifact | Authority | Assumptions / scope |
|---|---|---|
| Published manuscript v0.1-rc4 | Immutable tag at `1b4b506c9cb19d5fdbf9f59d89c7a179739d337d`; tagged PDF SHA-256 `624429bb0f2c211fec26cbc9e7608add65eb26a133a6af57259830b5fabd7693` | Historical E1/E2/E3 analytic candidate. |
| rc4 editorial artifact at intake main | Unchanged `archive/manuscripts/pre-eight-2026-10-30/paper/manuscript.tex`, PDF and label index; PDF SHA-256 `107f09155e1ce46d65b5f8070ce33d3d9eddb177120413883d91b4f9c12202e4` | Same frozen mathematics, later ORCID/bibliography edit; distinct bytes/pages from tagged rc4. [Crosswalk](../provenance/RC4_IDENTITY_2026-10-16.md). |
| Lean v0.2.1 | Immutable tag at `de23d9475744fb4625666142d5a03b3d688195e6` | Historical normalized endpoint takes E3; physical endpoint takes E1/E2/E3. |
| Verified manuscript v0.1-rc5 / Lean v0.3.0-rc1 | Immutable predecessor [`dd977048`](https://github.com/LeoLam233/ising-bulk-natural-boundary/tree/dd977048c2380e775d83b97ae1fba354c04c349a); manuscript source commit `a79c2f5701111b5234bbc0ff8481e75aec8c21d0` | Its source/PDF, local acceptance receipts and original open-comparison wording retain that identity. Later [full GitHub CI run 38962997911](https://github.com/LeoLam233/ising-bulk-natural-boundary/actions/runs/38962997911) accepted the same commit; those later remote logs are separate from the commit's local archive. [Preservation hashes](../provenance/AMPLITUDE_BASELINE.json). |
| Manuscript v0.1-rc6 | `archive/manuscripts/pre-eight-2026-10-30/paper/next/manuscript.tex` and matching PDF/index/BUILD.json; source commit `dce74bc7ce1106e96b0d754360ac9fbed5f2feea` | Current analytic candidate. All 67 rc5 label numbers retained; Proposition F.1 proves complete-amplitude conversion. |
| Lean v0.3.0-rc2 | Current sources, `lean/SOURCE.json`, `ci/accepted_identity.json` and `release/next/VALIDATION.json` | Current candidate; production Lean sources unchanged from dd977048. New source/configuration/verification identities and freshly executed receipts. Canonical E3 absent; physical E1/E2 retained. No release tag or main merge. |

The source commit identifies the manuscript snapshot, not a self-referential final release commit. Later commits bind verification configuration, documentation and receipts. Proof and verification identities bind their exact inputs independently of commit-message prose. [Current status](../release/CURRENT_STATUS.json).

The original rc4 `MANIFEST.json` is unchanged. The candidate `release/next/MANIFEST.json` inventories the final tracked tree except itself. `scripts/verify_candidate.py` checks that inventory, protected historical bytes, source/PDF/index identity, source snapshots and current semantic records. Hashes establish identity, not correctness.

Former current-facing Lean metadata and chronological notes are copied byte for byte under `lean/history/v0.2.1/`; `INDEX.json` binds every copy. The rc4 snapshot remains `lean/source_snapshot/manuscript.tex`; the rc5 snapshot `manuscript-rc5.tex` is retained, and the current snapshot is `manuscript-rc6.tex`. Historical reports, frozen evidence parts, scripts and original verdicts are not rewritten.

`audits/`, `reproduction/`, `research-history/`, older release records, `RELEASE_v0.2.0.md`, `REMEDIATION_v0.2.1.md`, the old expert brief and the history directory describe their own versions. Their “current”, “pending”, “PASS”, or stop language is local to those records. Current root documents and `release/next/` govern this candidate.

The v0.2.0 publication workflow and asset preparer remain historical, not a publisher for this candidate. Active acceptance workflows target the existing PR #3 branch `research/next-internal-regularity-20261017`. The separate amplitude research branch is checked locally before being fast-forwarded into that branch. No old CI success is reassigned to new bytes.

The versioned rc1 reports `UPGRADE_v0.3.0-rc1.md`, `MATHEMATICAL_AUDIT_v0.3.0-rc1.md` and `CONSISTENCY_AUDIT_v0.3.0-rc1.md` remain byte-identical. Their relative artifact links and words such as “current” describe the dd977048 tree; use the immutable predecessor link above to read them with their original assets. They do not describe rc6. The current [amplitude report](AMPLITUDE_IDENTIFICATION_v0.3.0-rc2.md), [mathematical audit](MATHEMATICAL_AUDIT_v0.3.0-rc2.md) and [consistency audit](CONSISTENCY_AUDIT_v0.3.0-rc2.md) distinguish the revisions. No materially different current PDF is presented as rc5.
