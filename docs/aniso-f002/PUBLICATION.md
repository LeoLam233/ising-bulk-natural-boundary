# ANISO-PSER F002: published Lean scope and provenance

[Alternative real-cycle manuscript](../../papers/fixed-ratio-anisotropy/README.md) ·
[Terminal module](../../lean/IsingBulk/AnisoF002/C03/FullUniformFieldConclusion.lean) ·
[Exact target contract](../../lean/IsingBulk/AnisoF002/Audit/C03FinalTargetContract.lean) ·
[Final audit bundle](../../lean/IsingBulk/AnisoF002/Audit/C03FinalReplayBundle.lean)

The Lean endpoint is `IsingBulk.AnisoF002.full_uniform_field_conclusion`. For
J > 0 and λ > 0, it proves the original
`FullUniformFieldConclusion J lam corrH corrL mH mL` with two explicit
published-real hypotheses. The target contract checks the terminal signature,
its fields, both physical interfaces, and that both real phase domains are
nonempty.

| Part | Exact scope |
|---|---|
| Analytic natural boundaries | On the high- and low-temperature domains `omegaH lam` and `omegaL lam`, the normalized susceptibility and the energy-field susceptibility each have a natural boundary. The proof covers every positive finite ratio, including λ = 1 by the internal F002 isotropic argument. `literal_fullAnalyticConclusion` needs only J, λ > 0. |
| Real full-lattice identification | For every positive noncritical real temperature on the relevant branch, the full correlation sum (HT) and the connected sum after subtracting M² (LT) are summable and equal the normalized susceptibility. The onsite terms are 1 and 1 − M², respectively. The energy-field normalization is χ = β𝒳, with β = x/(2J). |
| Uniform energy-field response | At zero field, the HT magnetization has a bilateral derivative and zero mean; the LT plus-phase magnetization has a right derivative, the specified zero-field square, and positive sign. The derivatives equal the respective energy-field susceptibilities. |

The input [`PublishedRealSpinFormFactors`](../../lean/IsingBulk/Anisotropic/FormFactors/PublishedRealInput.lean)
supplies the published pointwise, real-temperature zero-field representations.
[`PublishedRealGibbsFields`](../../lean/IsingBulk/Anisotropic/PhysicalField/PublishedRealGibbs.lean)
supplies the real Gibbs field conditions, high-temperature spin-flip symmetry,
and the two low-temperature zero-field magnetization facts. These are explicit
hypotheses; constructing their instances from the lattice Hamiltonian is
outside this terminal. The exported fields are as stated above; some finer
intermediate asymptotic statements in the frozen paper are stronger than the
exported Lean statements.

The 2026-11-02 accepted Lean snapshot uses Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. Its source manifest (4,267 files)
has SHA-256 `733133418727513bacbfa57161c1e964e2f28676de6f83dab688070419d26730`;
the terminal source has SHA-256
`4f3fb71a760039ef12836ce34abd321f866c250629ba347fd686bce1d4861a10`.
The integration adds its 825 absent files byte for byte. The earlier top-level
F002 and continuation roots are historical intermediate targets.

The audit used the frozen 52-page paper. Its PDF SHA-256 is
`b82149625b7c2223c743b8e7482f4818543a760b46decd845acdf217d7a2376c`,
and its TeX SHA-256 is
`7c0fc588a688869d0c95698ec67b989bf644f3bd0cb9ca1c7eb8624d3976c977`.
The existing 53-page editorial PDF and its TeX are the public reading edition.

- **Pro, 2026-11-03: `EXHAUSTED`** for the frozen paper and the exact conditional Lean terminal.
- **Codex, 2026-11-17: corrected `EXHAUSTED`; independent STOP-LOCK `APPROVE`.**
  The earlier `FAIL` was withdrawn because it required Lean to construct the
  two explicit physical inputs from the Hamiltonian, beyond the accepted
  target. The corrected audit verified their applicability and noncircularity
  and reported successful replay of the terminal module and its
  75,238-constant closure in an empty kernel. The reported reachable axioms
  were `propext`, `Classical.choice` and `Quot.sound`.

Build and replay the published terminal with the [current CI and build guide](../PROOF_CI_ROUTING.md#f002-proof).
