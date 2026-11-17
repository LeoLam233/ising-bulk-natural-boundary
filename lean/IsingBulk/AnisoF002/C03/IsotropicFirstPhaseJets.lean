import IsingBulk.AnisoF002.C03.IsotropicFirstDividedDifference
import IsingBulk.AnisoF002.C03.IsotropicFullPhysicalHomotopy

/-!
# Actual isotropic first-chart phase and its scalar jets

The chart is the literal physical angle -alpha+w and temperature
2 cos(alpha)+h.  Both scalar derivatives of the genuine logarithmic
root are forced by its unsquared cosh dispersion identity.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Filter IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology

def isotropicFirstDispersion (α : ℝ) (p : ℂ × ℂ) : ℂ :=
  (2 * Real.cos α : ℂ) + p.1 - Complex.cos (-(α : ℂ) + p.2)

def isotropicFirstLogPhase (α : ℝ) (p : ℂ × ℂ) : ℂ :=
  upperEdgePhase (isotropicFirstDispersion α p)

theorem isotropicFirstDispersion_center (α : ℝ) :
    isotropicFirstDispersion α (0, 0) = (Real.cos α : ℂ) := by
  simp only [isotropicFirstDispersion, add_zero, Complex.cos_neg, ← Complex.ofReal_cos]
  ring

theorem I_mul_upperPhysicalPhase (W : ℂ) :
    Complex.I * upperPhysicalPhase W = upperEdgePhase W := by
  unfold upperPhysicalPhase upperEdgePhase
  linear_combination (Complex.log (upperEdgeRoot W)) * Complex.I_sq

theorem isotropic_first_scalar_phase_jets {α : ℝ} (hα : 0 < α) (hπ : α < Real.pi) :
    AnalyticAt ℂ upperEdgePhase (Real.cos α : ℂ) ∧
    upperEdgePhase (Real.cos α : ℂ) = (α : ℂ) * Complex.I ∧
    deriv upperEdgePhase (Real.cos α : ℂ) = -Complex.I / (Real.sin α : ℂ) ∧
    deriv (deriv upperEdgePhase) (Real.cos α : ℂ) =
      -Complex.I * (Real.cos α : ℂ) / (Real.sin α : ℂ) ^ 3 := by
  have hsR : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα hπ
  have hs : (Real.sin α : ℂ) ≠ 0 := by exact_mod_cast hsR.ne'
  have hc : |Real.cos α| < 1 := by
    apply (sq_lt_one_iff_abs_lt_one _).mp
    nlinarith [Real.sin_sq_add_cos_sq α, sq_pos_of_pos hsR]
  have hslit : 1 - (Real.cos α : ℂ) ^ 2 ∈ Complex.slitPlane :=
    edge_discriminant_slit (Or.inr ⟨rfl, hc⟩)
  have hga := upperEdgePhase_analyticAt hslit
  have hgv := upperEdgePhase_cos hα hπ
  have hgd : deriv upperEdgePhase (Real.cos α : ℂ) = -Complex.I / (Real.sin α : ℂ) := by
    rw [(upperEdgePhase_hasDerivAt hslit).deriv, hgv,
      Complex.sinh_mul_I, ← Complex.ofReal_sin]
    field_simp
    simp [Complex.I_sq]
  have hfirst : (fun z => Complex.sinh (upperEdgePhase z) * deriv upperEdgePhase z)
      =ᶠ[𝓝 (Real.cos α : ℂ)] fun _ => (1 : ℂ) := by
    filter_upwards [hga.eventually_analyticAt] with z hz
    have hh := hz.differentiableAt.hasDerivAt.ccosh.deriv
    have hid : (fun w => Complex.cosh (upperEdgePhase w)) = (fun w : ℂ => w) :=
      funext upperEdgePhase_cosh
    rw [hid, deriv_id''] at hh
    exact hh.symm
  have hleft := hga.differentiableAt.hasDerivAt.csinh.mul hga.deriv.differentiableAt.hasDerivAt
  have hright := (hasDerivAt_const (Real.cos α : ℂ) (1 : ℂ)).congr_of_eventuallyEq hfirst
  have hsecond := hleft.unique hright
  have hsec : (Real.sin α : ℂ) * Complex.I * deriv (deriv upperEdgePhase) (Real.cos α : ℂ) =
      -(Real.cos α : ℂ) * (deriv upperEdgePhase (Real.cos α : ℂ)) ^ 2 := by
    rw [hgv, Complex.sinh_mul_I, Complex.cosh_mul_I,
      ← Complex.ofReal_sin, ← Complex.ofReal_cos] at hsecond
    linear_combination hsecond
  refine ⟨hga, hgv, hgd, ?_⟩
  apply mul_left_cancel₀ (mul_ne_zero hs Complex.I_ne_zero)
  rw [hsec, hgd]
  field_simp

theorem isotropicFirstLogPhase_analyticAt {α : ℝ} (hα : 0 < α) (hπ : α < Real.pi) :
    AnalyticAt ℂ (isotropicFirstLogPhase α) (0, 0) := by
  have hW : AnalyticAt ℂ (isotropicFirstDispersion α) (0, 0) :=
    (analyticAt_const.add analyticAt_fst).sub
      (Complex.analyticAt_cos.comp (analyticAt_const.add analyticAt_snd))
  exact (isotropic_first_scalar_phase_jets hα hπ).1.comp_of_eq hW
    (isotropicFirstDispersion_center α)

theorem isotropicFirstLogPhase_center {α : ℝ} (hα : 0 < α) (hπ : α < Real.pi) :
    isotropicFirstLogPhase α (0, 0) = (α : ℂ) * Complex.I := by
  rw [isotropicFirstLogPhase, isotropicFirstDispersion_center, upperEdgePhase_cos hα hπ]

end
end IsingBulk.AnisoF002.Isotropic
