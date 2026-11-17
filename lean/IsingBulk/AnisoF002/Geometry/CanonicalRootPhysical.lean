import IsingBulk.AnisoF002.Geometry.CanonicalRootContinuity
import Mathlib.Analysis.SpecialFunctions.Arcosh

/-!
# The canonical F002 root on both positive physical temperature intervals

The unsquared hyperbolic identity from F002 §1 and `lem:canonicalroot`
gives the strict real dispersion gap away from sinh(x)sinh(lam*x)=1.
The canonical root is then exactly exp(-arcosh W), the positive decaying
real physical branch, on both sides of that critical point.
-/

namespace IsingBulk.AnisoF002.Geometry
noncomputable section
open IsingBulk.Anisotropic

theorem real_spectral_factorization_f002 (lam x : ℝ) :
    (Real.cosh x * Real.cosh (lam * x) - Real.sinh x - Real.sinh (lam * x)) *
      (Real.cosh x * Real.cosh (lam * x) + Real.sinh x + Real.sinh (lam * x)) =
        (Real.sinh x * Real.sinh (lam * x) - 1) ^ 2 := by
  linear_combination (Real.cosh (lam * x)) ^ 2 * Real.cosh_sq_sub_sinh_sq x +
    ((Real.sinh x) ^ 2 + 1) * Real.cosh_sq_sub_sinh_sq (lam * x)

theorem positive_real_spectral_gap_f002 {lam x : ℝ} (hlam : 0 < lam) (hx : 0 < x)
    (hp : Real.sinh x * Real.sinh (lam * x) ≠ 1) :
    0 < Real.cosh x * Real.cosh (lam * x) - Real.sinh x - Real.sinh (lam * x) := by
  have hs : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  have ht : 0 < Real.sinh (lam * x) := Real.sinh_pos_iff.mpr (mul_pos hlam hx)
  have ha : 0 < Real.cosh x * Real.cosh (lam * x) :=
    mul_pos (Real.cosh_pos _) (Real.cosh_pos _)
  have hmul : 0 <
      (Real.cosh x * Real.cosh (lam * x) - Real.sinh x - Real.sinh (lam * x)) *
      (Real.cosh x * Real.cosh (lam * x) + Real.sinh x + Real.sinh (lam * x)) := by
    rw [real_spectral_factorization_f002]
    exact sq_pos_of_ne_zero (sub_ne_zero.mpr hp)
  exact pos_of_mul_pos_left hmul (by positivity)

theorem positive_real_not_mem_spectralSetF002 {lam x : ℝ} (hlam : 0 < lam) (hx : 0 < x)
    (hp : Real.sinh x * Real.sinh (lam * x) ≠ 1) :
    (x : ℂ) ∉ spectralSetF002 lam := by
  rintro ⟨u, hu, v, hv, he⟩
  have hre := congrArg Complex.re he
  change (Complex.cosh (x : ℂ) * Complex.cosh ((lam : ℂ) * (x : ℂ))).re =
    (Complex.sinh (x : ℂ) * (u : ℂ) +
      Complex.sinh ((lam : ℂ) * (x : ℂ)) * (v : ℂ)).re at hre
  simp only [← Complex.ofReal_mul,
    ← Complex.ofReal_cosh, ← Complex.ofReal_sinh, Complex.add_re, Complex.ofReal_re] at hre
  have hs : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  have ht : 0 < Real.sinh (lam * x) := Real.sinh_pos_iff.mpr (mul_pos hlam hx)
  have h₁ := mul_le_mul_of_nonneg_left hu.2 hs.le
  have h₂ := mul_le_mul_of_nonneg_left hv.2 ht.le
  have hg := positive_real_spectral_gap_f002 hlam hx hp
  nlinarith

def positiveRealSpectralW (lam x q : ℝ) : ℝ :=
  (Real.cosh x * Real.cosh (lam * x) - Real.sinh (lam * x) * Real.cos q) / Real.sinh x

theorem positiveRealSpectralW_gt_one {lam x : ℝ} (hlam : 0 < lam) (hx : 0 < x)
    (hp : Real.sinh x * Real.sinh (lam * x) ≠ 1) (q : ℝ) :
    1 < positiveRealSpectralW lam x q := by
  have hs : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  have ht : 0 < Real.sinh (lam * x) := Real.sinh_pos_iff.mpr (mul_pos hlam hx)
  have hg := positive_real_spectral_gap_f002 hlam hx hp
  have hcos := mul_le_mul_of_nonneg_left (Real.cos_le_one q) ht.le
  apply (lt_div_iff₀ hs).mpr
  linarith

theorem exp_neg_arcosh_reciprocal_polynomial {W : ℝ} (hW : 1 < W) :
    (Real.exp (-Real.arcosh W)) ^ 2 - 2 * W * Real.exp (-Real.arcosh W) + 1 = 0 ∧
      0 < Real.exp (-Real.arcosh W) ∧ Real.exp (-Real.arcosh W) < 1 := by
  have hform : Real.exp (-Real.arcosh W) = W - Real.sqrt (W ^ 2 - 1) := by
    rw [Real.exp_neg, Real.exp_arcosh hW.le, Real.add_sqrt_self_sq_sub_one_inv hW.le]
  refine ⟨?_, Real.exp_pos _, Real.exp_lt_one_iff.mpr (neg_neg_of_pos (Real.arcosh_pos hW))⟩
  rw [hform]
  have hsq := Real.sq_sqrt (show 0 ≤ W ^ 2 - 1 by nlinarith)
  nlinarith

/-- Physical positive-root identification on both HT and LT real intervals.
The only excluded positive temperature is the actual critical product. -/
theorem spectralSmallRootF002_physical {lam x : ℝ} (hlam : 0 < lam) (hx : 0 < x)
    (hp : Real.sinh x * Real.sinh (lam * x) ≠ 1) (q : ℝ) :
    spectralSmallRootF002 lam (x : ℂ) q =
      (Real.exp (-Real.arcosh (positiveRealSpectralW lam x q)) : ℂ) := by
  let W := positiveRealSpectralW lam x q
  let r := Real.exp (-Real.arcosh W)
  have hr := exp_neg_arcosh_reciprocal_polynomial (positiveRealSpectralW_gt_one hlam hx hp q)
  have hS : Real.sinh x ≠ 0 := (Real.sinh_pos_iff.mpr hx).ne'
  have hW : Real.sinh x * W =
      Real.cosh x * Real.cosh (lam * x) - Real.sinh (lam * x) * Real.cos q := by
    exact mul_div_cancel₀ _ hS
  have hpoly : Real.sinh x * r ^ 2 -
      2 * (Real.cosh x * Real.cosh (lam * x) - Real.sinh (lam * x) * Real.cos q) * r +
      Real.sinh x = 0 := by
    linear_combination Real.sinh x * hr.1 + 2 * r * hW
  symm
  apply spectralSmallRootF002_unique q (positive_real_not_mem_spectralSetF002 hlam hx hp)
  · delta spectralRootPolynomialF002 spectralA spectralS spectralT
    simp only [
      ← Complex.ofReal_mul, ← Complex.ofReal_cosh, ← Complex.ofReal_sinh]
    exact_mod_cast hpoly
  · simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.2.1] using hr.2.2

end
end IsingBulk.AnisoF002.Geometry
