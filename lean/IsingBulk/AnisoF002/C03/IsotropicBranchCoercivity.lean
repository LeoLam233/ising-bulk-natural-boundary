import IsingBulk.AnisoF002.C03.IsotropicBranchAttenuation

/-!
# Uniform size of the actual branch discriminant

The quadratic real remainder and positive attenuation give two-sided
control of 1-W by |u|+epsilon+h. This is the actual radial branch with
outward displacement, including u on either side of the branch point.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology
open Set Metric

def isotropicBranchDispersion (α b ε u h : ℝ) : ℂ :=
  isotropicDispersion (isotropicRadialParameter α ε,
    ((-b + u : ℝ) : ℂ) - Complex.I * (h : ℂ))

theorem exists_isotropic_branch_coercivity (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ r c C : ℝ, 0 < r ∧ r ≤ 1 ∧ 0 < c ∧ 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ u h : ℝ, |u| ≤ r → h ∈ Icc 0 r →
        c * (|u| + ε + h) ≤ ‖1 - isotropicBranchDispersion α b ε u h‖ ∧
        ‖1 - isotropicBranchDispersion α b ε u h‖ ≤ C * (|u| + ε + h) := by
  obtain ⟨rR, M, hrR, hM, hrem⟩ := exists_isotropic_branch_real_remainder α b hα hpoint
  obtain ⟨rA, cA, CA, hrA, hrA1, hcA, hCA, hatten⟩ :=
    exists_isotropic_branch_attenuation α b hα hb
  let a := Real.sin b
  have ha : 0 < a := Real.sin_pos_of_pos_of_lt_pi hb.1 hb.2
  let r := min (rR / 2) (min rA (min (a / (2 * M)) (cA / M)))
  let c := min (a / 8) (cA / 2)
  let C := a + M + CA
  have hr : 0 < r := lt_min (half_pos hrR)
    (lt_min hrA (lt_min (by positivity) (by positivity)))
  have hrR' : r ≤ rR / 2 := min_le_left _ _
  have hrA' : r ≤ rA := (min_le_right _ _).trans (min_le_left _ _)
  have hra : r ≤ a / (2 * M) := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hrc : r ≤ cA / M := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  have hr1 : r ≤ 1 := hrA'.trans hrA1
  have hMrA : M * r ≤ a / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * M)).mp hra
    nlinarith
  have hMrC : M * r ≤ cA := by
    have h := (le_div_iff₀ hM).mp hrc
    nlinarith
  have hc : 0 < c := lt_min (by positivity) (half_pos hcA)
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨r, c, C, hr, hr1, hc, hC, ?_⟩
  intro ε hε hεr u h hu hh
  let R := branchRealRemainder b (isotropicRadialParameter α ε) u h
  let β := branchAttenuation b (isotropicRadialParameter α ε) u h
  let z := 1 - isotropicBranchDispersion α b ε u h
  have hR : |R| ≤ M * (u ^ 2 + h ^ 2 + ε ^ 2) :=
    hrem ε hε (hεr.trans hr1) u h
      ((hu.trans hrR').trans_lt (half_lt_self hrR))
      (by rw [abs_of_nonneg hh.1]; exact (hh.2.trans hrR').trans_lt (half_lt_self hrR))
  obtain ⟨hβlo, hβhi⟩ := hatten ε hε (hεr.trans hrA') u h (hu.trans hrA')
    ⟨hh.1, hh.2.trans hrA'⟩
  change cA * (ε + h) ≤ β at hβlo
  change β ≤ CA * (ε + h) at hβhi
  have hβpos : 0 < β := (mul_pos hcA (by linarith [hh.1])).trans_le hβlo
  have hz : z = ((a * u + R : ℝ) : ℂ) - Complex.I * (β : ℂ) :=
    isotropic_branch_normal_identity b u h (isotropicRadialParameter α ε)
  have hzre : z.re = a * u + R := by
    rw [hz]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
  have hzim : z.im = -β := by
    rw [hz]
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, zero_add, zero_sub]
  have hreal : |a * u + R| ≤ ‖z‖ := by simpa only [hzre] using Complex.abs_re_le_norm z
  have himag : β ≤ ‖z‖ := by
    simpa only [hzim, abs_neg, abs_of_pos hβpos] using Complex.abs_im_le_norm z
  have hqu : u ^ 2 ≤ r * |u| := by nlinarith only [hu, sq_abs u, abs_nonneg u]
  have hqh : h ^ 2 ≤ r * h := by nlinarith only [hh.1, hh.2]
  have hqε : ε ^ 2 ≤ r * ε := by nlinarith only [hε, hεr]
  have hRsplit : |R| ≤ (a / 2) * |u| + cA * (ε + h) := by
    have hu' := mul_le_mul_of_nonneg_right hMrA (abs_nonneg u)
    have he' := mul_le_mul_of_nonneg_right hMrC (by linarith [hh.1] : 0 ≤ ε + h)
    have hquad := mul_le_mul_of_nonneg_left (by linarith : u ^ 2 + h ^ 2 + ε ^ 2 ≤
      r * |u| + r * (ε + h)) hM.le
    linarith only [hR, hquad, hu', he']
  have hau : a * |u| ≤ |a * u + R| + |R| := by
    have ht := abs_sub (a * u + R) R
    simpa only [add_sub_cancel_right, abs_mul, abs_of_pos ha] using ht
  have hauNorm : (a / 4) * |u| ≤ ‖z‖ := by linarith only [hau, hRsplit, hreal, hβlo, himag]
  have hcA := mul_le_mul_of_nonneg_right (min_le_left (a / 8) (cA / 2)) (abs_nonneg u)
  have hcβ := mul_le_mul_of_nonneg_right (min_le_right (a / 8) (cA / 2))
    (by linarith [hh.1] : 0 ≤ ε + h)
  constructor
  · change c * (|u| + ε + h) ≤ ‖z‖
    dsimp [c] at hcA hcβ ⊢
    linarith only [hcA, hcβ, hauNorm, hβlo, himag]
  · have hzu := Complex.norm_le_abs_re_add_abs_im z
    rw [hzre, hzim, abs_neg, abs_of_pos hβpos] at hzu
    have hsum := abs_add_le (a * u) R
    rw [abs_mul, abs_of_pos ha] at hsum
    have hqu1 : u ^ 2 ≤ |u| := by nlinarith only [hu, hr1, sq_abs u, abs_nonneg u]
    have hqh1 : h ^ 2 ≤ h := by nlinarith only [hh.1, hh.2, hr1]
    have hqε1 : ε ^ 2 ≤ ε := by nlinarith only [hε, hεr, hr1]
    have hquad := mul_le_mul_of_nonneg_left
      (by linarith : u ^ 2 + h ^ 2 + ε ^ 2 ≤ |u| + ε + h) hM.le
    have haε : 0 ≤ a * (ε + h) := mul_nonneg ha.le (by linarith [hh.1])
    have hCAu : 0 ≤ CA * |u| := mul_nonneg hCA.le (abs_nonneg u)
    change ‖z‖ ≤ C * (|u| + ε + h)
    dsimp [C]
    linarith only [hzu, hsum, hR, hquad, hβhi, haε, hCAu]

end IsingBulk.AnisoF002.Isotropic
