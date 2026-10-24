import IsingBulk.Anisotropic.Geometry.Isotropic
import IsingBulk.Anisotropic.Geometry.Profiles

namespace IsingBulk.Anisotropic
noncomputable section

theorem sinh_re_formula (z : ℂ) : (Complex.sinh z).re = Real.sinh z.re * Real.cos z.im := by
  conv_lhs => rw [← Complex.re_add_im z, Complex.sinh_add, Complex.cosh_mul_I,
    Complex.sinh_mul_I]
  simp [Complex.sinh_ofReal_re, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

theorem sinh_im_formula (z : ℂ) : (Complex.sinh z).im = Real.cosh z.re * Real.sin z.im := by
  conv_lhs => rw [← Complex.re_add_im z, Complex.sinh_add, Complex.cosh_mul_I,
    Complex.sinh_mul_I]
  simp [Complex.sinh_ofReal_re, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

theorem norm_sinh_sq (z : ℂ) : ‖Complex.sinh z‖^2 = Real.sinh z.re^2 + Real.sin z.im^2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, sinh_re_formula, sinh_im_formula]
  have h := Real.cosh_sq_sub_sinh_sq z.re
  have h' := Real.sin_sq_add_cos_sq z.im
  linear_combination Real.sin z.im^2 * h + Real.sinh z.re^2 * h'

theorem norm_sinh_lt_one_iff (z : ℂ) :
    ‖Complex.sinh z‖ < 1 ↔ |z.re| < Real.arsinh |Real.cos z.im| := by
  have hn := norm_nonneg (Complex.sinh z)
  have hs := Real.sin_sq_add_cos_sq z.im
  have hnorm := norm_sinh_sq z
  have hsin := Real.sinh_nonneg_iff.mpr (abs_nonneg z.re)
  have habs := abs_nonneg (Real.cos z.im)
  have hsq := sq_abs (Real.cos z.im)
  have hsq' : Real.sinh |z.re|^2 = Real.sinh z.re^2 := by rw [← Real.abs_sinh, sq_abs]
  conv_rhs => rw [← Real.sinh_lt_sinh, Real.sinh_arsinh]
  constructor <;> intro h <;> nlinarith

theorem norm_sinh_gt_one_iff {z : ℂ} (hz : 0 ≤ z.re) :
    1 < ‖Complex.sinh z‖ ↔ Real.arsinh |Real.cos z.im| < z.re := by
  have hn := norm_nonneg (Complex.sinh z)
  have hs := Real.sin_sq_add_cos_sq z.im
  have hnorm := norm_sinh_sq z
  have hsin := Real.sinh_nonneg_iff.mpr hz
  have habs := abs_nonneg (Real.cos z.im)
  have hsq := sq_abs (Real.cos z.im)
  conv_rhs => rw [← Real.sinh_lt_sinh, Real.sinh_arsinh]
  constructor <;> intro h <;> nlinarith

theorem mem_omegaH_one_iff (z : ℂ) :
    z ∈ omegaH 1 ↔ |z.im| < Real.pi/2 ∧ ‖Complex.sinh z‖ < 1 := by
  have hy : sliceY 1 = Real.pi/2 := by norm_num [sliceY]
  change (|z.im| < sliceY 1 ∧ |z.re| < sliceH 1 z.im) ↔ _
  rw [hy, sliceH_isotropic, norm_sinh_lt_one_iff]
  apply and_congr_right
  intro him
  have hc : 0 < Real.cos z.im := Real.cos_pos_of_mem_Ioo (abs_lt.mp him)
  rw [abs_of_pos hc]

theorem mem_omegaL_one_iff (z : ℂ) :
    z ∈ omegaL 1 ↔ 0 < z.re ∧ 1 < ‖Complex.sinh z‖ := by
  constructor
  · intro hz
    have hr := omegaL_re_pos (by norm_num : (0:ℝ)<1) hz
    refine ⟨hr, (norm_sinh_gt_one_iff hr.le).mpr ?_⟩
    simpa only [omegaL, Set.mem_ofPred_eq, sliceL_isotropic] using hz
  · rintro ⟨hr, hn⟩
    exact (show sliceL 1 z.im < z.re from by
      rw [sliceL_isotropic]
      exact (norm_sinh_gt_one_iff hr.le).mp hn)

end
end IsingBulk.Anisotropic
