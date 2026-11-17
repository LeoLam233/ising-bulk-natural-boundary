import IsingBulk.AnisoF002.C03.IsotropicFirstDenominator
import IsingBulk.AnisoF002.C03.IsotropicRadialApproach

/-!
# Exact analytic filling of the original isotropic exterior approach

The physical radial path remains t=(1+epsilon) exp(i alpha). Its S shift
is epsilon times one analytic scalar function with center 2 i sin(alpha).
This fills the actual radial denominator after the constrained scaling.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators

def isotropicRadialIncrement (α : ℝ) (e : ℂ) : ℂ :=
  ((Real.cos α : ℂ) * e + (Real.sin α : ℂ) * (2 + e) * Complex.I) / (1 + e)

theorem isotropicRadialIncrement_center (α : ℝ) :
    isotropicRadialIncrement α 0 = 2 * (Real.sin α : ℂ) * Complex.I := by
  simp only [isotropicRadialIncrement, mul_zero, add_zero, zero_add, div_one]
  ring

theorem isotropicRadialIncrement_analytic (α : ℝ) :
    AnalyticAt ℂ (isotropicRadialIncrement α) 0 := by
  exact ((analyticAt_const.mul analyticAt_id).add
    ((analyticAt_const.mul (analyticAt_const.add analyticAt_id)).mul analyticAt_const)).div
      (analyticAt_const.add analyticAt_id) (by norm_num)

theorem isotropicRadialParameter_filled (α e : ℝ) (he : 1 + e ≠ 0) :
    isotropicRadialParameter α e - (2 * Real.cos α : ℂ) =
      (e : ℂ) * isotropicRadialIncrement α (e : ℂ) := by
  have hec : (1 : ℂ) + (e : ℂ) ≠ 0 := by exact_mod_cast he
  rw [isotropicRadialParameter_formula]
  simp only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
    Complex.ofReal_inv, Complex.ofReal_one]
  unfold isotropicRadialIncrement
  field_simp [hec]
  ring

def isotropicRadialFilledDenominator {N : ℕ} (α : ℝ) (x : Fin N → ℂ)
    (weight : ℂ) (s : ℂ) : ℂ :=
  isotropicFirstBlowupDenominator α x
    (s, weight * isotropicRadialIncrement α (s ^ 2 * weight))

theorem isotropicRadialFilledDenominator_exact {N : ℕ} {α : ℝ}
    (hα : 0 < α) (hπ : α < Real.pi) (σ : ℂ)
    (hres : σ * Complex.exp (-((N : ℂ) * ((α : ℂ) * Complex.I))) = 1)
    (x : Fin N → ℂ) (hx : ∑ i, x i = 0) (s weight : ℝ)
    (he : 1 + s ^ 2 * weight ≠ 0) :
    isotropicFirstDenominator α σ
      (isotropicRadialParameter α (s ^ 2 * weight) - (2 * Real.cos α : ℂ),
        fun i => (s : ℂ) * x i) =
      (s : ℂ) ^ 2 * isotropicRadialFilledDenominator α x (weight : ℂ) (s : ℂ) := by
  rw [isotropicRadialParameter_filled α (s ^ 2 * weight) he]
  simp only [Complex.ofReal_mul, Complex.ofReal_pow]
  rw [mul_assoc]
  exact isotropicFirstDenominator_blowup hα hπ σ hres x hx _ _

theorem isotropicRadialFilledDenominator_center {N : ℕ} {α : ℝ}
    (hα : 0 < α) (hπ : α < Real.pi) (x : Fin N → ℂ) (weight : ℂ) :
    isotropicRadialFilledDenominator α x weight 0 =
      2 * (N : ℂ) * weight - Complex.I * (Real.cos α / Real.sin α : ℝ) * ∑ i, x i ^ 2 := by
  simp only [isotropicRadialFilledDenominator, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    zero_mul, isotropicRadialIncrement_center]
  rw [mul_comm weight]
  exact isotropicFirstBlowupDenominator_radial_center hα hπ x weight

theorem isotropicRadialFilledDenominator_analytic {N : ℕ} {α : ℝ}
    (hα : 0 < α) (hπ : α < Real.pi) (x : Fin N → ℂ) (weight : ℂ) :
    AnalyticAt ℂ (isotropicRadialFilledDenominator α x weight) 0 := by
  have ht : AnalyticAt ℂ (fun s : ℂ =>
      weight * isotropicRadialIncrement α (s ^ 2 * weight)) 0 :=
    analyticAt_const.mul ((isotropicRadialIncrement_analytic α).comp_of_eq
      ((analyticAt_id.pow 2).mul analyticAt_const) (by simp))
  exact (isotropicFirstBlowupDenominator_analytic hα hπ x _).comp_of_eq
    (analyticAt_id.prod ht) (by simp only [Prod.mk.injEq, true_and]; rfl)

end
end IsingBulk.AnisoF002.Isotropic
