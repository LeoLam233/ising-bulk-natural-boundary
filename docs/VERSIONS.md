# Authoritative versions and artifact identities

| Version / artifact | Authority | Assumptions / scope |
|---|---|---|
| Published manuscript v0.1-rc4 | Immutable tag at `1b4b506c9cb19d5fdbf9f59d89c7a179739d337d`; tagged PDF SHA-256 `624429bb0f2c211fec26cbc9e7608add65eb26a133a6af57259830b5fabd7693` | Historical E1/E2/E3 analytic candidate. |
| rc4 editorial artifact at intake main | Unchanged `paper/manuscript.tex`, PDF and label index; PDF SHA-256 `107f09155e1ce46d65b5f8070ce33d3d9eddb177120413883d91b4f9c12202e4` | Same frozen mathematics, later ORCID/bibliography edit; distinct bytes/pages from tagged rc4. [Crosswalk](../provenance/RC4_IDENTITY_2026-10-16.md). |
| Lean v0.2.1 | Immutable tag at `de23d9475744fb4625666142d5a03b3d688195e6` | Historical normalized endpoint takes E3; physical endpoint takes E1/E2/E3. |
| Manuscript v0.1-rc5 | `paper/next/manuscript.tex` and matching PDF/index/BUILD.json; source commit `a79c2f5701111b5234bbc0ff8481e75aec8c21d0` | Current analytic candidate. All 65 old label numbers retained. |
| Lean v0.3.0-rc1 | Current branch sources, `lean/SOURCE.json`, `ci/accepted_identity.json` and `release/next/VALIDATION.json` | Current candidate; normalized endpoint has no E3; physical identification retains E1/E2. No release tag or default-branch merge is created. |

The source commit identifies the manuscript snapshot, not a self-referential final release commit. Later commits bind verification configuration, documentation and receipts. Proof and verification identities bind their exact inputs independently of commit-message prose. [Current status](../release/CURRENT_STATUS.json).

The original rc4 `MANIFEST.json` is unchanged. The candidate `release/next/MANIFEST.json` inventories the final tracked tree except itself. `scripts/verify_candidate.py` checks that inventory, protected historical bytes, source/PDF/index identity, source snapshots and current semantic records. Hashes establish identity, not correctness.

Former current-facing Lean metadata and chronological notes are copied byte for byte under `lean/history/v0.2.1/`; `INDEX.json` binds every copy. The rc4 snapshot remains `lean/source_snapshot/manuscript.tex`; the new snapshot is `manuscript-rc5.tex`. Historical reports, frozen evidence parts, scripts and original verdicts are not rewritten.

`audits/`, `reproduction/`, `research-history/`, older release records, `RELEASE_v0.2.0.md`, `REMEDIATION_v0.2.1.md`, the old expert brief and the history directory describe their own versions. Their “current”, “pending”, “PASS”, or stop language is local to those records. Current root documents and `release/next/` govern this candidate.

The v0.2.0 publication workflow and asset preparer remain historical, not a publisher for this candidate. Active acceptance workflows include this development branch and record fresh results. No old CI success is reassigned to new bytes.
