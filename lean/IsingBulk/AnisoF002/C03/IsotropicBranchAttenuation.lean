import IsingBulk.AnisoF002.C03.IsotropicBranchRemainder

/-!
# Actual branch attenuation on the radial approach

The outward deformation and radial imaginary displacement add with the
same sign. Uniform positive lower and upper bounds are proved before
particle number or occupancy values enter the argument.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology
open Set Metric

theorem exists_sinh_linear_control :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧ ∀ h ∈ Icc 0 r,
      h ≤ Real.sinh h ∧ Real.sinh h ≤ C * h := by
  obtain ⟨r₀, M, hr₀, hM, hrem⟩ := analytic_scalar_quadratic_remainder Complex.sinh
    Complex.analyticAt_sinh
  let r := min (r₀ / 2) 1
  refine ⟨r, M + 1, lt_min (half_pos hr₀) zero_lt_one, by linarith, ?_⟩
  intro h hh
  have hh1 : h ≤ 1 := hh.2.trans (min_le_right _ _)
  have hh0 : |h| < r₀ := by
    rw [abs_of_nonneg hh.1]
    exact (hh.2.trans (min_le_left _ _)).trans_lt (half_lt_self hr₀)
  have hb := hrem (h : ℂ) (by simpa only [Complex.norm_real, Real.norm_eq_abs] using hh0)
  rw [(Complex.hasDerivAt_sinh 0).deriv] at hb
  simp only [Complex.sinh_zero, Complex.cosh_zero, one_mul, sub_zero] at hb
  have he : Complex.sinh (h : ℂ) - (h : ℂ) = ((Real.sinh h - h : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [he, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hb
  refine ⟨Real.self_le_sinh_iff.mpr hh.1, ?_⟩
  have hsq : h ^ 2 ≤ h := by nlinarith [hh.1]
  have hupper := le_abs_self (Real.sinh h - h)
  nlinarith [mul_le_mul_of_nonneg_left hsq hM.le]

theorem exists_isotropic_branch_attenuation (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi) :
    ∃ r c C : ℝ, 0 < r ∧ r ≤ 1 ∧ 0 < c ∧ 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ r → ∀ u h : ℝ, |u| ≤ r → h ∈ Icc 0 r →
        c * (ε + h) ≤ branchAttenuation b (isotropicRadialParameter α ε) u h ∧
        branchAttenuation b (isotropicRadialParameter α ε) u h ≤ C * (ε + h) := by
  have hsa : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα.1 hα.2
  have hsb : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb.1 hb.2
  obtain ⟨rh, Ch, hrh, hCh, hsinh⟩ := exists_sinh_linear_control
  let r := min rh (min 1 (Real.sin b / 2))
  let c := min (Real.sin α) (Real.sin b / 2)
  let C := 3 + Ch
  have hr : 0 < r := lt_min hrh (lt_min zero_lt_one (half_pos hsb))
  have hrh' : r ≤ rh := min_le_left _ _
  have hr1 : r ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hrs : r ≤ Real.sin b / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hc : 0 < c := lt_min hsa (half_pos hsb)
  refine ⟨r, c, C, hr, hr1, hc, by dsimp [C]; linarith, ?_⟩
  intro ε hε hεr u h hu hh
  obtain ⟨hslo, hshi⟩ := hsinh h ⟨hh.1, hh.2.trans hrh'⟩
  have hsinclose : |Real.sin (b - u) - Real.sin b| ≤ |u| := by
    simpa only [show b - u - b = -u by ring, abs_neg] using Real.abs_sin_sub_sin_le (b - u) b
  have hsinlo : Real.sin b / 2 ≤ Real.sin (b - u) := by
    have hh := (abs_le.mp hsinclose).1
    linarith [hu.trans hrs]
  have hβ := isotropicRadialParameter_estimates α ε hα hε (hεr.trans hr1)
  have htermlo : (Real.sin b / 2) * h ≤ Real.sinh h * Real.sin (b - u) := by
    have hh' := mul_le_mul hslo hsinlo (half_pos hsb).le (Real.sinh_nonneg_iff.mpr hh.1)
    nlinarith
  have htermhi : Real.sinh h * Real.sin (b - u) ≤ Ch * h := by
    exact (mul_le_mul_of_nonneg_left (Real.sin_le_one _) (Real.sinh_nonneg_iff.mpr hh.1)).trans
      (by simpa only [mul_one] using hshi)
  constructor
  · have hca := mul_le_mul_of_nonneg_right (min_le_left (Real.sin α) (Real.sin b / 2)) hε.le
    have hcb := mul_le_mul_of_nonneg_right (min_le_right (Real.sin α) (Real.sin b / 2)) hh.1
    dsimp [branchAttenuation]
    nlinarith [hβ.1]
  · dsimp [branchAttenuation, C]
    nlinarith [hβ.2.1, hh.1, mul_nonneg hCh.le hε.le]

end IsingBulk.AnisoF002.Isotropic
