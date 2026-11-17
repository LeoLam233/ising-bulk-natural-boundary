import IsingBulk.AnisoF002.C03.NegativeWindingSectorMajorants
import IsingBulk.AnisoF002.C03.NegativeCenterPeriod
import IsingBulk.AnisoF002.C03.NegativePhysicalTailAbsorption

/-!
# Exact normalization for the higher-winding comparison

The positive Beta majorant is compared with the modulus of the unchanged
first-winding model through its actual center and complete quadratic
period.  The common square-root sign is retained until taking its norm.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter MeasureTheory Angular
open scoped Topology BigOperators

theorem norm_centerDensityScalar (n : ℕ) (b : ℂ) {s : ℝ} (hs : 0 < s) :
    ‖centerDensityScalar n b s‖ =
      2 * ‖b‖ ^ (n ^ 2 - 2) /
        ((n : ℝ) * (n.factorial : ℝ) * (2 * Real.pi) ^ (n - 1) *
          (2 : ℝ) ^ (n * (n - 1)) * s ^ (n ^ 2 - 1)) := by
  simp only [centerDensityScalar, windingNormalization, norm_div, norm_neg, norm_mul,
    norm_pow, norm_natCast, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le, Real.norm_of_nonneg hs.le]
  ring

theorem centerDensityScalar_ne_zero {n : ℕ} (hn : 0 < n) {b : ℂ} (hb : b ≠ 0)
    {s : ℝ} (hs : 0 < s) : centerDensityScalar n b s ≠ 0 := by
  apply norm_pos_iff.mp
  rw [norm_centerDensityScalar n b hs]
  have hb' := norm_pos_iff.mpr hb
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  positivity

theorem allWindingCenterMagnitude_center_ratio {n : ℕ} (hn : 2 ≤ n)
    (b0 b1 : ℂ) (hb1 : b1 ≠ 0) {s : ℝ} (hs : 0 < s) (φ : ℝ)
    (hsφ : Real.sin φ = s) :
    allWindingCenterMagnitude n b0 φ =
      (n : ℝ) / (2 * s) * ‖b1‖ ^ 2 * (‖b0‖ / ‖b1‖) ^ (n ^ 2) *
        ‖centerDensityScalar n b1 s‖ := by
  have hbpos := norm_pos_iff.mpr hb1
  have hN : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsq : 2 ≤ n ^ 2 := by nlinarith
  have hp : ‖b1‖ ^ (n ^ 2) = ‖b1‖ ^ (n ^ 2 - 2) * ‖b1‖ ^ 2 := by
    rw [← pow_add, Nat.sub_add_cancel hsq]
  have hsp : s ^ (n ^ 2) = s ^ (n ^ 2 - 1) * s := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n ^ 2)]
  rw [allWindingCenterMagnitude, hsφ, norm_centerDensityScalar n b1 hs, div_pow, hp, hsp]
  field_simp

theorem norm_modelCoefficient_center_period {l : ℕ} (hl : 0 < l) (m : ℕ)
    {b B h : ℂ} (hB : B ≠ 0) (hb : b ^ 2 = B)
    {s τ : ℝ} (hs : 0 < s) (hτ : 0 < τ) (hh : 0 < h.re) :
    ‖modelCoefficient (2 * l + 1) (2 * l * (l + 1) + m) B h s τ‖ =
      2 * ‖centerDensityScalar (2 * l + 1) b s‖ *
        (constrainedGaussianIntegral (2 * l) * (m.factorial : ℝ) /
          (((2 * l * (l + 1) + m).factorial : ℝ) *
            (‖h‖ / (2 * ((2 * l + 1 : ℕ) : ℝ))) ^ (2 * l * (l + 1)) * τ ^ (m + 1))) := by
  have hN : (0 : ℝ) < ((2 * l + 1 : ℕ) : ℝ) := by positivity
  have hhc : 0 < (h / (2 * ((2 * l + 1 : ℕ) : ℂ))).re := by
    rw [show (2 : ℂ) * ((2 * l + 1 : ℕ) : ℂ) =
      ((2 * ((2 * l + 1 : ℕ) : ℝ) : ℝ) : ℂ) by push_cast; rfl,
      Complex.div_ofReal_re]
    exact div_pos hh (by positivity)
  have he := congrArg norm (twice_center_quadratic_period_model hl m hB hb hs.ne' hτ hh)
  simp only [norm_mul, Complex.norm_ofNat, physical_root_branch_sign_norm hB hb, one_mul] at he
  rw [integral_quadraticPeriod_odd_particles hl m hτ hhc] at he
  simp only [norm_mul, norm_div, norm_pow, norm_natCast, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_of_nonneg (constrainedGaussianIntegral_pos (2 * l)).le,
    Real.norm_of_nonneg hτ.le] at he
  exact he.symm

end
end IsingBulk.AnisoF002.NegativeHT
