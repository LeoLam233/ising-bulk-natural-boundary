# v0.1-rc4: W2 proof repairs and E1 source closure

Prepared 1 October 2026 for public mathematical review. Public predecessor: `v0.1-rc3`, commit `c36735380a9746bba5e84f9b6adec2a494d1fd4c`. The mathematical baseline for this metadata-only release preparation is `59881ee24f43b8caab60f81ab3f87f758cfc03d5`.

Compared with public rc3, rc4 incorporates two distinct changes:

**W2 proof-interface repairs**, integrated at `fc0f82d127081cc372b84ebcfac48da9f5ccd79f`:

- explicit B/L/R support geometry and strict same-group contraction;
- local root continuation and regular double-branch treatment;
- reserved disk slack and tau-dependent protected disk restriction;
- direct remaining-pair recount and coupled-occupancy bookkeeping;
- Lemma 7.3 pair estimates explicitly confined to K and named-Stokes supports, rather than the unrestricted original torus.

These are substantive proof-interface repairs. See the frozen [W2 phase record](provenance/W2_REPAIR_AUDIT.md).

**E1 source-interface closure**, integrated at `59881ee24f43b8caab60f81ab3f87f758cfc03d5`:

- Palmer–Tracy's infinite-volume + boundary-condition state and its spin-flip relation to the - state;
- published Tracy–Widom 2014 normalization, determinant/sign explanations and Appendix 1 source locators;
- exact fixed-N full-site/offsite relation `C_N^std=f00^(N)+2T_N`;
- the arXiv-v1-only normalization discrepancy confined to provenance and history.

E1 is source/exposition integration closing a scoped interface, not a new theorem proof. See the frozen [E1 phase record](provenance/E1_SOURCE_CLOSURE.md).

The theorem statement, selected cyclotomic point family, derivative range and particle-number windows are unchanged relative to rc3. Release preparation preserves all mathematical source content at `59881ee...`, including `eq:double`, `eq:bulk` and W1/W2/E1 derivations.

This remains an AI-assisted candidate proof without independent human, peer or proof-assistant certification. Finite diagnostics and hashes do not prove uniform analytic or infinite-tail claims. Older audit verdicts remain tied to their input versions; no exhaustive novelty or priority clearance is claimed.

The proposed tag is `v0.1-rc4`; release preparation creates no tag or publication. [Rc4 release-prep status](release/RC4_RELEASE_PREP_STATUS.json), [validation](release/RC4_RELEASE_PREP_VALIDATION.json) and [static scholarly status](release/STATUS.json) distinguish preparation from mathematical certification. Older release-note sections below retain their exact bytes.

---

# v0.1-rc3

The mathematical content is frozen at `813c6b9a21872ab5358d3da5cbbd99ed05210cf9`, following rc2 baseline `47f95a386d329ae6a3e377fecceafde78ea0886c`. Subsequent metadata changes preserve that mathematical content.

Compared with rc2, rc3 contains substantive repairs to the W1 intermediate-window proof interfaces:

- an explicit small-lambda Stokes-current partition;
- a remaining-pair recount after differentiation, without division by removed factors;
- the corrected near-region branch-slope cost;
- a lambda-deformed branch normal form allowing branch-center displacement;
- expanded constant-dependency and epsilon0 bookkeeping.

The theorem statement, physical observable, selected cyclotomic point family, derivative range and particle-number windows are unchanged. These are substantive proof-interface repairs, not merely typographical corrections.

Rc3 remains an AI-assisted candidate proof. The W1 repairs received a scoped AI analytic recheck and edited-text regression; this is not independent human review, peer review or proof-assistant certification. The complete natural-boundary theorem remains independently uncertified. Finite diagnostics do not prove continuous-domain or infinite-tail estimates. Older audit verdicts apply only to their audited versions.

See the historical [release-prep status](release/RC3_RELEASE_PREP_STATUS.json) and [validation](release/RC3_RELEASE_PREP_VALIDATION.json), and the [W1 repair record](provenance/W1_REPAIR_AUDIT.md). The following candidate and rc2 notes are preserved as historical records.

---

# v0.1-rc3-unreleased candidate notes

Local W1 repair candidate from baseline `47f95a386d329ae6a3e377fecceafde78ea0886c`, prepared 30 September 2026. No tag or release is created.

The revision adds an explicit small-lambda current partition, a remaining-pair contraction interface, corrected near-region slope costs and a uniform deformed branch normal form. It also simplifies the microcore integral and records all constant dependencies and final smallness choices. The theorem, observable, derivative range and particle windows are unchanged.

See the [scoped AI audit and repair record](provenance/W1_REPAIR_AUDIT.md) and [candidate validation](release/W1_CANDIDATE_VALIDATION.json). Human and proof-assistant certification remain absent.

---

# v0.1-rc2 release notes

Candidate for public mathematical review. Evidence snapshot: 28 September 2026. This version preserves the mathematics of revision 8 / v0.1-rc1 and makes editorial, bibliographic and release-presentation changes.

- Adds the primary-source-checked Orrick–Nickel–Guttmann–Perk 2001 discussion as evidence and heuristic precedent, not a rigorous bulk noncancellation theorem.
- Clarifies that literature-priority clearance is not exhaustive. Existing mathematical statements, proof routes and external premises are unchanged.
- Makes README reading order math-first and merges the optimized two-page expert brief with synchronized version and references.
- Uses conservative AI/authorship disclosure, static scholarly release status and clear license wording.
- Adds an index explaining historical AI audit names/verdicts. Historical views, reconstruction outputs, scripts, source inventories, prior search logs and negative findings retain their rc1 bytes.

The three CR0 runs remain PARTIAL. MR1 still claims a tail proof while I3 is unresolved and I6 conditional; receiver checks did not certify the entire tail. Historical access evidence and technical isolation remain incomplete. No favorable audit verdict is promoted to peer review or certification of this version.

See [rc2 validation](release/RC2_VALIDATION.md), [source delta](provenance/RC1_RC2_MANUSCRIPT_DELTA.json), [primary-source verification](provenance/ORRICK_2001_VERIFICATION.md), and [audit index](audits/README.md). The [final-public assembly validation](release/FINAL_PUBLIC_VALIDATION.md) records the integration of expert brief v0.1-rc3 with manuscript v0.1-rc2. Earlier release checks, including the linked rc2 preparation records, remain historical records for their original input hashes. Finite computations and file hashes do not certify the infinite-tail proof.
