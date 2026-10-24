import IsingBulk.Anisotropic.Geometry.Inverses

namespace IsingBulk.Anisotropic
noncomputable section

def criticalPoint (lam : ℝ) : ℝ := slicePInv lam 1

@[simp] theorem slicePInv_zero {lam : ℝ} (hlam : 0 < lam) : slicePInv lam 0 = 0 := by
  simpa using sliceP_inv_apply hlam 0
@[simp] theorem sliceQInv_zero {lam : ℝ} (hlam : 0 < lam) : sliceQInv lam 0 = 0 := by
  simpa using sliceQ_inv_apply hlam 0

theorem criticalPoint_pos {lam : ℝ} (hlam : 0 < lam) : 0 < criticalPoint lam := by
  simpa [criticalPoint, slicePInv_zero hlam] using slicePInv_strictMono hlam (by norm_num : (0:ℝ)<1)

theorem sinh_product_criticalPoint {lam : ℝ} (hlam : 0 < lam) :
    Real.sinh (criticalPoint lam) * Real.sinh (lam * criticalPoint lam) = 1 := by
  let x := criticalPoint lam
  have hx : 0 < x := criticalPoint_pos hlam
  have hp : sliceP lam x = 1 := sliceP_apply_inv hlam 1
  have hc : Real.cosh x * Real.sinh (lam*x) = Real.cosh (lam*x) := by
    unfold sliceP at hp
    rw [Real.tanh_eq_sinh_div_cosh, ← mul_div_assoc] at hp
    exact (div_eq_one_iff_eq (ne_of_gt (Real.cosh_pos _))).mp hp
  have h1 := Real.cosh_sq_sub_sinh_sq x
  have h2 := Real.cosh_sq_sub_sinh_sq (lam*x)
  have hsq : (Real.sinh x * Real.sinh (lam*x))^2 = 1 := by
    linear_combination -Real.sinh (lam*x)^2 * h1 + h2 +
      (Real.cosh x * Real.sinh (lam*x) + Real.cosh (lam*x)) * hc
  have hnonneg : 0 ≤ Real.sinh x * Real.sinh (lam*x) := by positivity
  nlinarith

theorem sliceQ_criticalPoint {lam : ℝ} (hlam : 0 < lam) :
    sliceQ lam (criticalPoint lam) = 1 := by
  let x := criticalPoint lam
  have hx : 0 < x := criticalPoint_pos hlam
  have hp : Real.sinh x * Real.sinh (lam*x) = 1 := sinh_product_criticalPoint hlam
  have h1 := Real.cosh_sq_sub_sinh_sq x
  have h2 := Real.cosh_sq_sub_sinh_sq (lam*x)
  have hsq : (Real.cosh (lam*x) * Real.sinh x)^2 = Real.cosh x^2 := by
    linear_combination Real.sinh x^2 * h2 - h1 +
      (Real.sinh x * Real.sinh (lam*x) + 1) * hp
  have hc : Real.cosh (lam*x) * Real.sinh x = Real.cosh x := by
    have hh : 0 ≤ Real.cosh (lam*x) * Real.sinh x := by positivity
    have hh' := Real.cosh_pos x
    nlinarith
  unfold sliceQ
  rw [Real.tanh_eq_sinh_div_cosh, ← mul_div_assoc]
  exact (div_eq_one_iff_eq (ne_of_gt (Real.cosh_pos _))).mpr hc

theorem sliceQInv_one {lam : ℝ} (hlam : 0 < lam) : sliceQInv lam 1 = criticalPoint lam := by
  rw [← sliceQ_criticalPoint hlam, sliceQ_inv_apply hlam]

theorem sliceL_nonneg {lam : ℝ} (hlam : 0 < lam) (y : ℝ) : 0 ≤ sliceL lam y := by
  apply le_trans ?_ (le_max_left _ _)
  simpa only [slicePInv_zero hlam] using (slicePInv_strictMono hlam).monotone (abs_nonneg (Real.cos y))

theorem sliceL_le_criticalPoint {lam : ℝ} (hlam : 0 < lam) (y : ℝ) :
    sliceL lam y ≤ criticalPoint lam := by
  apply max_le
  · exact (slicePInv_strictMono hlam).monotone (Real.abs_cos_le_one y)
  · rw [← sliceQInv_one hlam]
    exact (sliceQInv_strictMono hlam).monotone (Real.abs_cos_le_one (lam*y))

theorem sliceL_continuous {lam : ℝ} (hlam : 0 < lam) : Continuous (sliceL lam) := by
  exact ((slicePInv_continuous hlam).comp Real.continuous_cos.abs).max
    ((sliceQInv_continuous hlam).comp ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).abs))

theorem sliceH_continuous {lam : ℝ} (hlam : 0 < lam) : Continuous (sliceH lam) := by
  exact ((slicePInv_continuous hlam).comp Real.continuous_cos).min
    ((sliceQInv_continuous hlam).comp (Real.continuous_cos.comp (continuous_const.mul continuous_id)))

theorem omegaL_re_pos {lam : ℝ} (hlam : 0 < lam) {z : ℂ} (hz : z ∈ omegaL lam) : 0 < z.re :=
  lt_of_le_of_lt (sliceL_nonneg hlam z.im) hz

theorem omegaL_isOpen {lam : ℝ} (hlam : 0 < lam) : IsOpen (omegaL lam) :=
  isOpen_lt ((sliceL_continuous hlam).comp Complex.continuous_im) Complex.continuous_re

theorem omegaH_isOpen {lam : ℝ} (hlam : 0 < lam) : IsOpen (omegaH lam) :=
  (isOpen_lt Complex.continuous_im.abs continuous_const).inter
    (isOpen_lt Complex.continuous_re.abs ((sliceH_continuous hlam).comp Complex.continuous_im))

end
end IsingBulk.Anisotropic
