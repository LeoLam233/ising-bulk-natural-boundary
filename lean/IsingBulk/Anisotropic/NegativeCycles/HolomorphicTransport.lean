import IsingBulk.Anisotropic.NegativeCycles.HolomorphicClosed

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open Set

/-- Literal real pullback of the holomorphic complex top form along the chain. -/
def chainPullback {n : ℕ}
    (ω : (Fin n → ℂ) → (Fin n → ℂ) [⋀^Fin n]→L[ℂ] ℂ)
    (H : ParameterSpace n → Fin n → ℂ) (x : ParameterSpace n) :
    ParameterSpace n [⋀^Fin n]→L[ℝ] ℂ :=
  ((ω (H x)).restrictScalars ℝ).compContinuousLinearMap (fderiv ℝ H x)

theorem chainPullback_differentiableAt {n : ℕ}
    {ω : (Fin n → ℂ) → (Fin n → ℂ) [⋀^Fin n]→L[ℂ] ℂ}
    {H : ParameterSpace n → Fin n → ℂ} {x : ParameterSpace n}
    (hω : DifferentiableAt ℂ ω (H x)) (hH : ContDiffAt ℝ 2 H x) :
    DifferentiableAt ℝ (chainPullback ω H) x := by
  let L : ((Fin n → ℂ) [⋀^Fin n]→L[ℂ] ℂ) →L[ℝ]
      ((Fin n → ℂ) [⋀^Fin n]→L[ℝ] ℂ) :=
    (ContinuousAlternatingMap.restrictScalarsLI ℝ).toContinuousLinearMap
  have hr := L.differentiableAt.comp (H x) (hω.restrictScalars ℝ)
  exact (hr.comp x (hH.differentiableAt (by norm_num))).continuousAlternatingMapCompContinuousLinearMap
    ((hH.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))

theorem chainPullback_closed {n : ℕ}
    {ω : (Fin n → ℂ) → (Fin n → ℂ) [⋀^Fin n]→L[ℂ] ℂ}
    {H : ParameterSpace n → Fin n → ℂ} {x : ParameterSpace n}
    (hω : DifferentiableAt ℂ ω (H x)) (hH : ContDiffAt ℝ 2 H x) :
    extDeriv (chainPullback ω H) x=0 := by
  let L : ((Fin n → ℂ) [⋀^Fin n]→L[ℂ] ℂ) →L[ℝ]
      ((Fin n → ℂ) [⋀^Fin n]→L[ℝ] ℂ) :=
    (ContinuousAlternatingMap.restrictScalarsLI ℝ).toContinuousLinearMap
  have hr : DifferentiableAt ℝ (fun y => (ω y).restrictScalars ℝ) (H x) :=
    L.differentiableAt.comp (H x) (hω.restrictScalars ℝ)
  unfold chainPullback
  rw [extDeriv_pullback hr hH (by norm_num [minSmoothness]),holomorphic_top_form_closed hω]
  ext v
  rfl

/-- Genuine holomorphic-chain Stokes theorem, including all side faces. -/
theorem holomorphic_chain_boundary_zero {n : ℕ}
    (ω : (Fin n → ℂ) → (Fin n → ℂ) [⋀^Fin n]→L[ℂ] ℂ)
    (H : ParameterSpace n → Fin n → ℂ) {a b : ParameterSpace n} (hab : a≤b)
    (hω : ∀x∈Icc a b, DifferentiableAt ℂ ω (H x))
    (hH : ∀x∈Icc a b, ContDiffAt ℝ 2 H x) :
    boxBoundaryFlux (chainPullback ω H) a b=0 :=
  boxBoundaryFlux_eq_zero _ hab
    (fun x hx => chainPullback_differentiableAt (hω x hx) (hH x hx))
    (fun x hx => chainPullback_closed (hω x hx) (hH x hx))

end IsingBulk.Anisotropic.NegativeCycles
