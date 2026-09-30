# A candidate natural-boundary proof for the bulk Ising susceptibility

**v0.1-rc4-unreleased · Local unpublished candidate · Dehao Lin**

[中文说明](README.zh.md) · [Paper PDF](paper/manuscript.pdf) · [Standalone TeX](paper/manuscript.tex) · [Two-page expert brief](docs/expert_brief.pdf)

## Object and claim

This repository presents an AI-assisted candidate proof concerning the **zero-field, isotropic, infinite square-lattice bulk susceptibility**, continued from its low-temperature pure-phase exterior germ. It claims that the unit circle in $s=\sinh(2\beta_{\rm phys}J)$ is a natural boundary. The observable includes all lattice separations and the entire even-particle expansion. See [precise claims](CLAIMS.md) and [external premises](provenance/EXTERNAL_PREMISES.md).

## Historical gap

Nickel identified fixed-form-factor singularities whose union is dense on the unit circle. Orrick, Nickel, Guttmann and Perk supplied further amplitude-based evidence against cancellation, explicitly short of a proof. Tracy–Widom proved fixed-even-order smoothness away from Nickel points and rigorous natural-boundary results for diagonal susceptibility and Toeplitz sums. The rigorous gap targeted here is control of the infinite higher-particle tail; fixed-order singularities alone do not exclude cancellation. Sources and their distinct roles are in [prior art](provenance/PRIOR_ART.md).

## Two load-bearing estimates

At each fixed selected point $s_{\ast}$ of manuscript §3, set $N_0=2p$, $k=N_0^2/2-1$ and $s_\epsilon=(1+\epsilon)s_{\ast}$. The manuscript claims

$$
\partial_s^k T_{N_0}(s_\epsilon)=2L_\beta\epsilon^{-1/2}+o(\epsilon^{-1/2}),\qquad L_\beta\ne0,
$$

$$
\sum_{N>N_0,\quad N\text{ even}}|\partial_s^j T_N(s_\epsilon)|=o(\epsilon^{-1/2}),\qquad 0\le j\le k.
$$

The first supplies a nonzero singular carrier; the second makes the entire higher-particle tail too small to cancel it. Constants may depend on the fixed point and finite $k$. These are the proof claims to scrutinize, not externally certified estimates.

## Proof architecture

The dense uniquely-first family leads to a nonzero **whole-form-factor** first singularity. In parallel, the exact weighted contour identity $T_N=F_N+K_N+S_N$ leads to differentiated control of all higher even orders. With the lower-order bounds and exterior normal convergence, the two branches give noncancellation on a dense boundary set and the claimed natural boundary. [Proof guide](docs/PROOF_GUIDE.md); manuscript §§3–9 and Appendices B–G.

## Proposed contribution and prior precedents

The divergent-first-term / controlled-tail strategy is established prior work in Tracy–Widom's diagonal-susceptibility analysis. Their Toeplitz work also provides close precedents for contour partitions, Vandermonde analysis, grouping and Hadamard/factorial estimates. This manuscript's proposed technical contribution is the **specific implementation for full bulk susceptibility**: the selected point family, compatible whole-integral first-amplitude calculation, coupled weighted contours, protected parameter disks and differentiated full-tail/coarea estimates. Correctness and priority for these details remain open to scrutiny. No exhaustive priority clearance is claimed.

## Status and limitations

This is an `UNRELEASED_LOCAL_CANDIDATE`. The W2 revision makes pair geometry, root continuation, disk slack and coupled differentiation explicit. E1 source closure remains pending. [Current candidate status](release/W2_CANDIDATE_STATUS.json).

| Evidence | Status and limit in this candidate snapshot |
|---|---|
| Manuscript | Candidate complete argument with historical [W1 repairs](provenance/W1_REPAIR_AUDIT.md) and local [W2 repairs](provenance/W2_REPAIR_AUDIT.md). |
| AI adversarial audits | Earlier errors prompted repairs. Favorable verdicts apply only to their input versions and checked scope; they are not peer review or current certification. |
| Problem-only CR0 | Three returned runs, all `PARTIAL`; complete natural-boundary reconstructions: **0/3**. |
| Method-informed MR1 | One `CLAIMED_TAIL_PROOF`; I3 unresolved, I6 conditional. Receiver checks did **not** independently certify the entire tail proof. |
| Finite computations | Reproducible algebra and numerical diagnostics; no continuous-domain or infinite-tail certification. |
| Human / formal review | No independent human expert certification or proof-assistant verification recorded. |

These counts are workflow records, not correctness probabilities. Runs may share model priors; technical isolation was not independently established. Different point families cannot be silently spliced. [Limitations](LIMITATIONS.md) · [historical release-prep status](release/RC3_RELEASE_PREP_STATUS.json).

## How to scrutinize

Choose one interface: first carrier and complement (§4, App. B); exact weighted contours and protected pair control (§§5–8); high-order differentiation, flux and coarea (Apps. D–E); or complete W1–W13 tail closure (§9, App. G). A concrete failing configuration, unjustified implication or uniformity step, or missed close precedent is especially useful. A limited reading of one interface is valuable; full refereeing is not presumed. [Feedback guidance](CONTRIBUTING.md).

## Audit, reconstruction and provenance

The [audit index](audits/README.md) explains the historical names and verdicts without rewriting them. The [version ledger](audits/VERSION_LEDGER.md), [CR0/MR1 records](reproduction/README.md), [source history](provenance/SOURCE_PROVENANCE.md), and [raw source inventory](provenance/V38_SOURCE_INVENTORY.json) preserve both favorable and negative findings. Historical access records are incomplete; no zero-exposure or exhaustive source-cleanliness certification is claimed.

From the repository root:

```sh
python scripts/verify_repository.py
python -m pip install -r requirements.txt
python scripts/reproduce.py
```

Outputs go to `.local/`, leaving evidence unchanged. Hashes establish identity; finite diagnostics do not prove the theorem. [Check scope](checks/README.md) · [build instructions](paper/README.md) · [historical release-prep validation](release/RC3_RELEASE_PREP_VALIDATION.json) · [frozen candidate validation](release/W1_CANDIDATE_VALIDATION.json) · [historical rc2 validation](release/FINAL_PUBLIC_VALIDATION.md).

## Citation, authorship and license

Dehao Lin is the named human author and public contact. Generative AI was used extensively in exploration, derivations, writing, code and internal audits. [Authorship and declarations](AUTHORSHIP.md) · [versioned citation](CITATION.cff).

Code: [MIT](LICENSE). Manuscript and project-authored prose: [CC BY 4.0](LICENSE-DOCUMENTATION.md). Third-party cited works retain their own rights; full external papers are not bundled. [Third-party notices](THIRD_PARTY_NOTICES.md).
