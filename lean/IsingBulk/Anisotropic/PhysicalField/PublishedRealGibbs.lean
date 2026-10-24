import IsingBulk.Anisotropic.PhysicalField.GibbsFieldConditions

/-! Typed real Gibbs-field entry data. These are external real physical
representations, not axioms or complex ANISO conclusions. They supplement,
and are not inferred from, the zero-field form-factor representation.

Sources: Camia--Garban--Newman, arXiv:1205.6612v4, Theorem 1.5 and Corollary 1.6
(arbitrary nonnegative edge interactions and site fields, including pinned plus
spins); Friedli--Velenik, Statistical Mechanics of Lattice Systems, Chapter 3,
(3.20), Theorems 3.20--3.21, Lemma 3.22 and the proof of Theorem 3.17.
The finite local laws are Gibbs marginals and the volume laws are plus-boundary
finite-volume distributions, with energy field -h sum sigma. Their physical
couplings are Jx=J and Jy=lam*J, and beta=x/(2J). The zero-field plus mean is
fixed by the same real form-factor vacuum normalization as the connected sum.

No field derivative, susceptibility summability, complex continuation,
normal-form estimate or natural boundary is included below. The finite-law
calculus and thermodynamic squeeze are proved in the imported modules. -/
namespace IsingBulk.Anisotropic.PhysicalField
noncomputable section
open FormFactors

structure PublishedRealGibbsFields (J lam : ℝ)
    (corrH corrL : ℝ → LatticeSite → ℝ) (mH mL : ℝ → ℝ → ℝ) : Prop where
  high : ∀ x, 0<x → realProduct lam x<1 →
    Nonempty (GibbsFieldConditions (x/(2*J)) (corrH x) (mH x))
  low : ∀ x, 0<x → 1<realProduct lam x →
    Nonempty (GibbsFieldConditions (x/(2*J))
      (fun v => corrL x v-realMagnetizationSq lam x) (mL x))
  high_spin_flip : ∀ x, 0<x → realProduct lam x<1 → ∀ h, mH x (-h)= -mH x h
  low_zero_square : ∀ x, 0<x → 1<realProduct lam x → (mL x 0)^2=realMagnetizationSq lam x
  low_plus_positive : ∀ x, 0<x → 1<realProduct lam x → 0<mL x 0

end
end IsingBulk.Anisotropic.PhysicalField
