import IsingBulk.AnisoF002.C03.IsotropicObliqueCube

/-!
# The frozen 3 pi / 8 projection and stability under the actual numerator

The rotation is exactly the one in frozen F002's extreme-coordinate
coarea argument. Its quantitative positivity survives the small complex
variation of the physical curvature numerator.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology

def frozenObliqueAngle : ℝ := 3 * Real.pi / 8

def frozenObliqueRotation : ℂ :=
  Complex.exp (-Complex.I * (frozenObliqueAngle : ℂ))

theorem frozenObliqueAngle_cos_pos : 0 < Real.cos frozenObliqueAngle := by
  apply Real.cos_pos_of_mem_Ioo
  dsimp [frozenObliqueAngle]
  constructor <;> linarith only [Real.pi_pos]

theorem frozenObliqueAngle_sin_ge_two_cos :
    2 * Real.cos frozenObliqueAngle ≤ Real.sin frozenObliqueAngle := by
  have hs : 0 ≤ Real.sin frozenObliqueAngle := by
    apply Real.sin_nonneg_of_mem_Icc
    dsimp [frozenObliqueAngle]
    constructor <;> linarith only [Real.pi_pos]
  have hc := frozenObliqueAngle_cos_pos
  have hdouble : Real.cos (2 * frozenObliqueAngle) = -Real.sqrt 2 / 2 := by
    rw [show 2 * frozenObliqueAngle = Real.pi - Real.pi / 4 by dsimp [frozenObliqueAngle]; ring,
      Real.cos_pi_sub, Real.cos_pi_div_four]
    ring
  have hcos := Real.cos_two_mul frozenObliqueAngle
  rw [hdouble] at hcos
  have hsum := Real.sin_sq_add_cos_sq frozenObliqueAngle
  have hsqrt : (6 / 5 : ℝ) ≤ Real.sqrt 2 := by
    have hh := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hn := Real.sqrt_nonneg (2 : ℝ)
    nlinarith only [hh, hn]
  have hsq : (2 * Real.cos frozenObliqueAngle) ^ 2 ≤ (Real.sin frozenObliqueAngle) ^ 2 := by
    nlinarith only [hcos, hsum, hsqrt]
  exact (sq_le_sq₀ (by positivity) hs).mp hsq

theorem frozenObliqueRotation_eq :
    frozenObliqueRotation = (Real.cos frozenObliqueAngle : ℂ) -
      Complex.I * (Real.sin frozenObliqueAngle : ℂ) := by
  unfold frozenObliqueRotation
  rw [show -Complex.I * (frozenObliqueAngle : ℂ) = (-(frozenObliqueAngle : ℂ)) * Complex.I by ring,
    Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  ring

theorem frozenObliqueRotation_norm : ‖frozenObliqueRotation‖ = 1 := by
  unfold frozenObliqueRotation
  rw [Complex.norm_exp]
  simp

theorem frozen_projection_reciprocal_cube_lower (z : ℂ)
    (hx : 0 < z.re) (hy : z.im ≤ 0) (hyx : -z.im ≤ (11 / 10 : ℝ) * z.re) :
    Real.cos frozenObliqueAngle / (27 * ‖z‖ ^ 3) ≤ (frozenObliqueRotation / z ^ 3).re := by
  rw [frozenObliqueRotation_eq]
  exact oblique_reciprocal_cube_lower z _ _ hx hy hyx frozenObliqueAngle_cos_pos
    frozenObliqueAngle_sin_ge_two_cos

/-- The genuine complex numerator may vary; its entire error is
controlled in norm and absorbed into the positive frozen projection. -/
theorem frozen_projection_curvature_perturbation (z q : ℂ) (n : ℝ)
    (hx : 0 < z.re) (hy : z.im ≤ 0) (hyx : -z.im ≤ (11 / 10 : ℝ) * z.re)
    (hn : 0 < n) (hq : ‖q - (n : ℂ)‖ ≤ n * Real.cos frozenObliqueAngle / 54) :
    n * Real.cos frozenObliqueAngle / (54 * ‖z‖ ^ 3) ≤
      (frozenObliqueRotation * (q / z ^ 3)).re := by
  have hz : z ≠ 0 := by intro h; simp only [h, Complex.zero_re] at hx; exact hx.false
  have hzNorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hbase := frozen_projection_reciprocal_cube_lower z hx hy hyx
  have hbase' := mul_le_mul_of_nonneg_left hbase hn.le
  have herr : -(‖q - (n : ℂ)‖ / ‖z‖ ^ 3) ≤
      (frozenObliqueRotation * ((q - (n : ℂ)) / z ^ 3)).re := by
    have hh := (abs_le.mp (Complex.abs_re_le_norm
      (frozenObliqueRotation * ((q - (n : ℂ)) / z ^ 3)))).1
    simpa only [norm_mul, norm_div, norm_pow, frozenObliqueRotation_norm, one_mul] using hh
  have herr' := div_le_div_of_nonneg_right hq (pow_nonneg (norm_nonneg z) 3)
  have he : (frozenObliqueRotation * (q / z ^ 3)).re =
      n * (frozenObliqueRotation / z ^ 3).re +
        (frozenObliqueRotation * ((q - (n : ℂ)) / z ^ 3)).re := by
    have hh : frozenObliqueRotation * (q / z ^ 3) =
        (n : ℂ) * (frozenObliqueRotation / z ^ 3) +
          frozenObliqueRotation * ((q - (n : ℂ)) / z ^ 3) := by ring
    rw [hh, Complex.add_re, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [he]
  have hdiv : n * (Real.cos frozenObliqueAngle / (27 * ‖z‖ ^ 3)) -
      (n * Real.cos frozenObliqueAngle / 54) / ‖z‖ ^ 3 =
        n * Real.cos frozenObliqueAngle / (54 * ‖z‖ ^ 3) := by ring
  linarith only [hbase', herr, herr', hdiv]

end IsingBulk.AnisoF002.Isotropic
