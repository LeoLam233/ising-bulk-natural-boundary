import IsingBulk.Anisotropic.NegativeCycles.BoxStokes
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Analysis.Complex.Basic

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles

/-- Restriction of scalars preserves the actual exterior derivative of a holomorphic form. -/
theorem extDeriv_restrictScalars_complex {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {n : ℕ} {ω : E → E [⋀^Fin n]→L[ℂ] ℂ} {x : E}
    (hω : DifferentiableAt ℂ ω x) :
    extDeriv (fun y => (ω y).restrictScalars ℝ) x=(extDeriv ω x).restrictScalars ℝ := by
  let L : (E [⋀^Fin n]→L[ℂ] ℂ) →L[ℝ] (E [⋀^Fin n]→L[ℝ] ℂ) :=
    (ContinuousAlternatingMap.restrictScalarsLI ℝ).toContinuousLinearMap
  have hr : DifferentiableAt ℝ (fun y => (ω y).restrictScalars ℝ) x :=
    L.differentiableAt.comp x
      (hω.restrictScalars ℝ)
  ext v
  rw [extDeriv_apply hr]
  change (∑ i, (-1:ℤ)^i.val •
      fderiv ℝ (fun y => ω y (i.removeNth v)) x (v i))=extDeriv ω x v
  rw [extDeriv_apply hω]
  apply Finset.sum_congr rfl
  intro i _
  have he := (hω.hasFDerivAt.continuousAlternatingMap_apply_const (i.removeNth v)).differentiableAt
  rw [(he.hasFDerivAt.restrictScalars ℝ).fderiv]
  rfl

/-- A holomorphic top-dimensional complex form is genuinely closed as a real form. -/
theorem holomorphic_top_form_closed {n : ℕ}
    {ω : (Fin n → ℂ) → (Fin n → ℂ) [⋀^Fin n]→L[ℂ] ℂ} {x : Fin n → ℂ}
    (hω : DifferentiableAt ℂ ω x) :
    extDeriv (fun y => (ω y).restrictScalars ℝ) x=0 := by
  rw [extDeriv_restrictScalars_complex hω]
  have hz : extDeriv ω x=0 := by
    ext v
    apply (extDeriv ω x).toAlternatingMap.map_linearDependent
    intro hv
    have hh := hv.fintype_card_le_finrank
    simp only [Fintype.card_fin,Module.finrank_pi] at hh
    omega
  rw [hz]
  ext v
  rfl

end IsingBulk.Anisotropic.NegativeCycles
