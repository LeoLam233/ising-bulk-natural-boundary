import IsingBulk.Anisotropic.Geometry.DomainNonvanishing

namespace IsingBulk.Anisotropic
noncomputable section

theorem sinh_ne_zero_of_re_pos {z : ℂ} (hz : 0<z.re) : Complex.sinh z ≠ 0 := by
  intro he
  have h := norm_sinh_sq z
  rw [he,norm_zero,zero_pow (by decide : 2≠0)] at h
  have hp := sq_pos_of_pos (Real.sinh_pos_iff.mpr hz)
  nlinarith [sq_nonneg (Real.sin z.im)]

theorem omegaL_product_ne_zero {lam : ℝ} (hlam : 0<lam) {z : ℂ} (hz : z∈omegaL lam) :
    spectralProduct lam z ≠ 0 := by
  apply mul_ne_zero (sinh_ne_zero_of_re_pos (omegaL_re_pos hlam hz))
  apply sinh_ne_zero_of_re_pos
  simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    using mul_pos hlam (omegaL_re_pos hlam hz)

theorem sliceL_zero {lam : ℝ} (hlam : 0<lam) : sliceL lam 0=criticalPoint lam := by
  simp [sliceL,sliceQInv_one hlam,criticalPoint]

theorem real_mem_omegaL_iff {lam : ℝ} (hlam : 0<lam) (x : ℝ) :
    (x:ℂ)∈omegaL lam ↔ criticalPoint lam<x := by
  change sliceL lam (x:ℂ).im < (x:ℂ).re ↔ _
  rw [Complex.ofReal_re,Complex.ofReal_im,sliceL_zero hlam]

theorem real_product_strictMonoOn {lam : ℝ} (hlam : 0<lam) :
    StrictMonoOn (fun x:ℝ => Real.sinh x*Real.sinh (lam*x)) (Set.Ici 0) := by
  intro a ha b hb hab
  have hbpos : 0<b := lt_of_le_of_lt ha hab
  have hHa := Real.sinh_nonneg_iff.mpr ha
  have hHb := Real.sinh_pos_iff.mpr (mul_pos hlam hbpos)
  calc
    Real.sinh a*Real.sinh (lam*a) ≤ Real.sinh a*Real.sinh (lam*b) :=
      mul_le_mul_of_nonneg_left (Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_left hab.le hlam.le)) hHa
    _ < Real.sinh b*Real.sinh (lam*b) := mul_lt_mul_of_pos_right (Real.sinh_lt_sinh.mpr hab) hHb

theorem criticalPoint_lt_iff_product_gt_one {lam : ℝ} (hlam : 0<lam) {x : ℝ} (hx : 0≤x) :
    criticalPoint lam<x ↔ 1<Real.sinh x*Real.sinh (lam*x) := by
  rw [← (real_product_strictMonoOn hlam).lt_iff_lt (criticalPoint_pos hlam).le hx,
    sinh_product_criticalPoint hlam]

theorem real_mem_omegaL_iff_product_gt_one {lam : ℝ} (hlam : 0<lam) {x : ℝ} (hx : 0≤x) :
    (x:ℂ)∈omegaL lam ↔ 1<Real.sinh x*Real.sinh (lam*x) := by
  rw [real_mem_omegaL_iff hlam,criticalPoint_lt_iff_product_gt_one hlam hx]

end
end IsingBulk.Anisotropic
