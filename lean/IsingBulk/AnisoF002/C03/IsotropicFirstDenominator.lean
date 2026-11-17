import IsingBulk.AnisoF002.C03.IsotropicFirstPhaseBlowup

/-!
# Exact physical first denominator at the isotropic resonance

This is the original product of physical roots, with its signed kernel.
The filled exponential gives an exact weighted blow-up, not a replacement
denominator. The central quadratic term has the required perpendicular
radial and shape phases on the original real constraint plane.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators

def isotropicExpFill (z : ℂ) : ℂ := dslope Complex.exp 0 z

@[simp] theorem isotropicExpFill_zero : isotropicExpFill 0 = 1 := by
  simp [isotropicExpFill, Complex.deriv_exp]

theorem isotropicExpFill_exact (z : ℂ) :
    z * isotropicExpFill z = Complex.exp z - 1 := by
  simpa only [isotropicExpFill, sub_zero, smul_eq_mul, Complex.exp_zero] using
    sub_smul_dslope Complex.exp 0 z

theorem isotropicExpFill_analytic_zero : AnalyticAt ℂ isotropicExpFill 0 :=
  analyticAt_dslope_center analyticAt_id.cexp

def isotropicFirstDenominator {N : ℕ} (α : ℝ) (σ : ℂ)
    (p : ℂ × (Fin N → ℂ)) : ℂ :=
  1 - σ * ∏ i, upperEdgeRoot (isotropicFirstDispersion α (p.1, p.2 i))

def isotropicFirstBlowupDenominator {N : ℕ} (α : ℝ) (x : Fin N → ℂ)
    (p : ℂ × ℂ) : ℂ :=
  isotropicFirstBlowupTotal α x p *
    isotropicExpFill (-(p.1 ^ 2 * isotropicFirstBlowupTotal α x p))

theorem isotropicFirstDenominator_physical {N : ℕ} (α : ℝ) (σ h : ℂ)
    (x : Fin N → ℂ) :
    isotropicFirstDenominator α σ (h, x) =
      1 - σ * ∏ i, isotropicInteriorRoot
        ((2 * Real.cos α : ℂ) + h, -(α : ℂ) + x i) := rfl

theorem isotropicFirstDenominator_exp {N : ℕ} (α : ℝ) (σ : ℂ)
    (p : ℂ × (Fin N → ℂ)) :
    isotropicFirstDenominator α σ p =
      1 - σ * Complex.exp (-(∑ i, isotropicFirstLogPhase α (p.1, p.2 i))) := by
  simp only [isotropicFirstDenominator, isotropicFirstLogPhase,
    ← upperEdgePhase_exp_neg, ← Complex.exp_sum, Finset.sum_neg_distrib]

theorem isotropicFirstDenominator_blowup {N : ℕ} {α : ℝ}
    (hα : 0 < α) (hπ : α < Real.pi) (σ : ℂ)
    (hres : σ * Complex.exp (-((N : ℂ) * ((α : ℂ) * Complex.I))) = 1)
    (x : Fin N → ℂ) (hx : ∑ i, x i = 0) (s t : ℂ) :
    isotropicFirstDenominator α σ (s ^ 2 * t, fun i => s * x i) =
      s ^ 2 * isotropicFirstBlowupDenominator α x (s, t) := by
  have hp := isotropicFirstBlowupTotal_exact hα hπ x hx s t
  have hsum : (∑ i, isotropicFirstLogPhase α (s ^ 2 * t, s * x i)) =
      (N : ℂ) * ((α : ℂ) * Complex.I) + s ^ 2 * isotropicFirstBlowupTotal α x (s, t) := by
    linear_combination hp
  rw [isotropicFirstDenominator_exp, hsum, neg_add, Complex.exp_add, ← mul_assoc, hres,
    one_mul]
  have he := isotropicExpFill_exact (-(s ^ 2 * isotropicFirstBlowupTotal α x (s, t)))
  unfold isotropicFirstBlowupDenominator
  linear_combination he

theorem isotropicFirstBlowupDenominator_analytic {N : ℕ} {α : ℝ}
    (hα : 0 < α) (hπ : α < Real.pi) (x : Fin N → ℂ) (t : ℂ) :
    AnalyticAt ℂ (isotropicFirstBlowupDenominator α x) (0, t) := by
  have hP := isotropicFirstBlowupTotal_analytic hα hπ x t
  have he : AnalyticAt ℂ (fun p : ℂ × ℂ =>
      isotropicExpFill (-(p.1 ^ 2 * isotropicFirstBlowupTotal α x p))) (0, t) :=
    isotropicExpFill_analytic_zero.comp_of_eq (((analyticAt_fst.pow 2).mul hP).neg) (by simp)
  exact hP.mul he

theorem isotropicFirstBlowupDenominator_center {N : ℕ} {α : ℝ}
    (hα : 0 < α) (hπ : α < Real.pi) (x : Fin N → ℂ) (t : ℂ) :
    isotropicFirstBlowupDenominator α x (0, t) =
      -Complex.I / (Real.sin α : ℂ) * (N : ℂ) * t -
        Complex.I * (Real.cos α : ℂ) / (Real.sin α : ℂ) * ∑ i, x i ^ 2 := by
  simp only [isotropicFirstBlowupDenominator, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    zero_mul, neg_zero, isotropicExpFill_zero, mul_one,
    isotropicFirstBlowupTotal_center hα hπ]

theorem isotropicFirstBlowupDenominator_radial_center {N : ℕ} {α : ℝ}
    (hα : 0 < α) (hπ : α < Real.pi) (x : Fin N → ℂ) (weight : ℂ) :
    isotropicFirstBlowupDenominator α x (0, 2 * (Real.sin α : ℂ) * Complex.I * weight) =
      2 * (N : ℂ) * weight - Complex.I * (Real.cos α / Real.sin α : ℝ) * ∑ i, x i ^ 2 := by
  have hs : (Real.sin α : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sin_pos_of_pos_of_lt_pi hα hπ).ne'
  rw [isotropicFirstBlowupDenominator_center hα hπ]
  rw [Complex.ofReal_div]
  field_simp [hs]
  ring_nf
  simp [Complex.I_sq]

end
end IsingBulk.AnisoF002.Isotropic
