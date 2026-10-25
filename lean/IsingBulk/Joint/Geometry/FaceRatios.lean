import IsingBulk.Joint.Geometry.FaceParameterBase

namespace IsingBulk.Joint
noncomputable section

def faceRatio1 (v : ℝ × ℝ) : ℝ := Real.cosh v.1 * Real.tanh |v.2|
def faceRatio2 (v : ℝ × ℝ) : ℝ := Real.cosh v.2 * Real.tanh |v.1|

@[fun_prop] theorem faceRatio1_continuous : Continuous faceRatio1 := by unfold faceRatio1; fun_prop
@[fun_prop] theorem faceRatio2_continuous : Continuous faceRatio2 := by unfold faceRatio2; fun_prop

theorem cosh_abs_eq (x : ℝ) : Real.cosh |x| = Real.cosh x := by
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h,Real.cosh_neg]

theorem faceRatio1_lt_one_iff (v : ℝ × ℝ) : faceRatio1 v < 1 ↔ realProduct v < 1 := by
  unfold faceRatio1 realProduct
  rw [← cosh_abs_eq v.1]
  exact real_edge_high_iff (abs_nonneg _) (abs_nonneg _)

theorem faceRatio2_lt_one_iff (v : ℝ × ℝ) : faceRatio2 v < 1 ↔ realProduct v < 1 := by
  unfold faceRatio2 realProduct
  rw [← cosh_abs_eq v.2,real_edge_high_iff (abs_nonneg _) (abs_nonneg _),mul_comm]

theorem faceRatio1_pos {v : ℝ × ℝ} (h : v.2 ≠ 0) : 0 < faceRatio1 v := by
  apply mul_pos (Real.cosh_pos _)
  simpa using IsingBulk.Anisotropic.tanh_strictMono (abs_pos.mpr h)

theorem faceRatio2_pos {v : ℝ × ℝ} (h : v.1 ≠ 0) : 0 < faceRatio2 v := by
  apply mul_pos (Real.cosh_pos _)
  simpa using IsingBulk.Anisotropic.tanh_strictMono (abs_pos.mpr h)

theorem cosine_scaled_arccos_gt {r a : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (ha : |a| < 1) :
    r < Real.cos (a * Real.arccos r) := by
  have hpos := Real.arccos_pos.mpr hr1
  have hpi := Real.arccos_le_pi r
  have hlt : |a * Real.arccos r| < Real.arccos r := by
    rw [abs_mul,abs_of_pos hpos]
    nlinarith
  have hc := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg _) hpi hlt
  rw [Real.cos_arccos (by linarith) hr1.le,Real.cos_abs] at hc
  exact hc

theorem scaled_arccos_strip {r a : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (ha : |a| < 1) :
    |a * Real.arccos r| < Real.pi/2 := by
  have hpos := Real.arccos_pos.mpr hr1
  have hpi := Real.arccos_le_pi_div_two.mpr hr
  rw [abs_mul,abs_of_pos hpos]
  nlinarith

end
end IsingBulk.Joint
