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
