import IsingBulk.Joint.Geometry.Components

namespace IsingBulk.Joint
noncomputable section

theorem real_edge_high_iff {x u : ℝ} (hx : 0 ≤ x) (hu : 0 ≤ u) :
    Real.cosh x * Real.tanh u < 1 ↔ Real.sinh x * Real.sinh u < 1 := by
  rw [Real.tanh_eq_sinh_div_cosh, ← mul_div_assoc, div_lt_one (Real.cosh_pos u)]
  have h₁ := Real.cosh_sq_sub_sinh_sq x
  have h₂ := Real.cosh_sq_sub_sinh_sq u
  have hid : (Real.cosh x*Real.sinh u)^2 - Real.cosh u^2 =
      (Real.sinh x*Real.sinh u)^2-1 := by
    linear_combination Real.sinh u^2*h₁-h₂
  have hn : 0 ≤ Real.cosh x*Real.sinh u := by positivity
  have hp : 0 ≤ Real.sinh x*Real.sinh u := by positivity
  have hc := Real.cosh_pos u
  constructor <;> intro h <;> nlinarith

theorem real_edge_low_iff {x u : ℝ} (hx : 0 ≤ x) (hu : 0 ≤ u) :
    1 < Real.cosh x * Real.tanh u ↔ 1 < Real.sinh x * Real.sinh u := by
  rw [Real.tanh_eq_sinh_div_cosh, ← mul_div_assoc, one_lt_div (Real.cosh_pos u)]
  have h₁ := Real.cosh_sq_sub_sinh_sq x
  have h₂ := Real.cosh_sq_sub_sinh_sq u
  have hid : (Real.cosh x*Real.sinh u)^2 - Real.cosh u^2 =
      (Real.sinh x*Real.sinh u)^2-1 := by
    linear_combination Real.sinh u^2*h₁-h₂
  have hn : 0 ≤ Real.cosh x*Real.sinh u := by positivity
  have hp : 0 ≤ Real.sinh x*Real.sinh u := by positivity
  have hc := Real.cosh_pos u
  constructor <;> intro h <;> nlinarith

theorem realPositive_mem_high_iff {x u : ℝ} (hx : 0 < x) (hu : 0 < u) :
    ((x:ℂ),(u:ℂ)) ∈ highDomain ↔ Real.sinh x*Real.sinh u < 1 := by
  simp only [highDomain,Set.mem_ofPred_eq,Complex.ofReal_im,Complex.ofReal_re,
    abs_zero,Real.cos_zero,abs_of_pos hx,abs_of_pos hu]
  rw [real_edge_high_iff hx.le hu.le,real_edge_high_iff hu.le hx.le,mul_comm (Real.sinh u)]
  have hp : (0:ℝ) < Real.pi/2 := by positivity
  simp only [hp,true_and,and_self]

theorem realPositive_mem_low_iff {x u : ℝ} (hx : 0 < x) (hu : 0 < u) :
    ((x:ℂ),(u:ℂ)) ∈ lowDomain ↔ 1 < Real.sinh x*Real.sinh u := by
  simp only [lowDomain,Set.mem_ofPred_eq,Complex.ofReal_im,Complex.ofReal_re,
    Real.cos_zero,abs_one,hx,hu,true_and]
  rw [real_edge_low_iff hx.le hu.le,real_edge_low_iff hu.le hx.le,mul_comm (Real.sinh u)]
  simp only [and_self]

end
end IsingBulk.Joint
