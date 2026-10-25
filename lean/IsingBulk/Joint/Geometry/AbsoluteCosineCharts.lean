import IsingBulk.Joint.Geometry.HighFaceParameter
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

namespace IsingBulk.Joint
noncomputable section

/-- Every real angle lies in an actual translated/reflected principal cosine chart. -/
theorem cosine_chart_representation (y : ℝ) :
    ∃ k : ℤ, ∃ sgn : ℝ, (sgn = -1 ∨ sgn = 1) ∧
      y = 2*(k:ℝ)*Real.pi + sgn*Real.arccos (Real.cos y) := by
  have hc : Real.cos (Real.arccos (Real.cos y)) = Real.cos y :=
    Real.cos_arccos (Real.neg_one_le_cos _) (Real.cos_le_one _)
  obtain ⟨k,h | h⟩ := Real.cos_eq_cos_iff.mp hc
  · exact ⟨k,1,Or.inr rfl,by simpa using h⟩
  · exact ⟨k,-1,Or.inl rfl,by simpa [sub_eq_add_neg] using h⟩

/-- This parametrization retains both cosine signs and every π-period. -/
theorem abs_cos_chart_representation {y r : ℝ} (hr : |Real.cos y| = r) :
    ∃ k : ℤ, ∃ sgn : ℝ, (sgn = -1 ∨ sgn = 1) ∧
      y = (k:ℝ)*Real.pi + sgn*Real.arccos r := by
  obtain ⟨k,sgn,hs,he⟩ := cosine_chart_representation y
  by_cases hc : 0 ≤ Real.cos y
  · have hcr : Real.cos y = r := by simpa only [abs_of_nonneg hc] using hr
    refine ⟨2*k,sgn,hs,?_⟩
    rw [hcr] at he
    simpa only [Int.cast_mul,Int.cast_ofNat,mul_assoc] using he
  · have hcr : Real.cos y = -r := by rw [abs_of_neg (lt_of_not_ge hc)] at hr; linarith
    rw [hcr,Real.arccos_neg] at he
    rcases hs with hs | hs
    · refine ⟨2*k-1,1,Or.inr rfl,?_⟩
      rw [hs] at he
      push_cast
      linear_combination he
    · refine ⟨2*k+1,-1,Or.inl rfl,?_⟩
      rw [hs] at he
      push_cast
      linear_combination he

theorem abs_cos_chart (k : ℤ) {sgn r : ℝ} (hs : sgn = -1 ∨ sgn = 1)
    (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    |Real.cos ((k:ℝ)*Real.pi + sgn*Real.arccos r)| = r := by
  rw [add_comm,Real.cos_add_int_mul_pi,abs_mul]
  have hk : |(-1:ℝ)^k| = 1 := by simp
  rw [hk,one_mul,cos_sign_mul _ _ hs,Real.cos_arccos (by linarith) hr1,abs_of_nonneg hr]

/-- The free coordinate's allowable interval is centered at a cosine zero. -/
theorem cosine_free_chart_representation {y r : ℝ} (hr : 0 ≤ r) (_hr1 : r ≤ 1)
    (hy : |Real.cos y| ≤ r) :
    ∃ k : ℤ, ∃ sgn a : ℝ, (sgn = -1 ∨ sgn = 1) ∧ |a| ≤ 1 ∧
      y = 2*(k:ℝ)*Real.pi + sgn*(Real.pi/2+a*(Real.pi/2-Real.arccos r)) := by
  obtain ⟨k,sgn,hs,he⟩ := cosine_chart_representation y
  let θ := Real.arccos (Real.cos y)
  let R := Real.pi/2-Real.arccos r
  have hR : 0 ≤ R := sub_nonneg.mpr (Real.arccos_le_pi_div_two.mpr hr)
  have hθ : |θ-Real.pi/2| ≤ R := by
    have hupper := Real.arccos_le_arccos (abs_le.mp hy).1
    have hlower := Real.arccos_le_arccos (abs_le.mp hy).2
    rw [Real.arccos_neg] at hupper
    dsimp [θ,R]
    apply abs_le.mpr
    constructor <;> linarith
  obtain ⟨a,ha,hea⟩ : ∃ a : ℝ, |a| ≤ 1 ∧ a*R = θ-Real.pi/2 := by
    by_cases hz : R = 0
    · have heq : θ-Real.pi/2 = 0 := by rw [hz] at hθ; exact abs_nonpos_iff.mp hθ
      exact ⟨0,by norm_num,by simp [heq]⟩
    · have hp := lt_of_le_of_ne hR (Ne.symm hz)
      refine ⟨(θ-Real.pi/2)/R,?_,div_mul_cancel₀ _ hz⟩
      rw [abs_div,abs_of_pos hp,div_le_one hp]
      exact hθ
  refine ⟨k,sgn,a,hs,ha,?_⟩
  change y = 2*(k:ℝ)*Real.pi+sgn*(Real.pi/2+a*R)
  rw [hea]
  simpa only [add_sub_cancel] using he


theorem cosine_free_chart_strict (k : ℤ) {sgn r a : ℝ}
    (hs : sgn = -1 ∨ sgn = 1) (hr : 0 < r) (hr1 : r < 1) (ha : |a| < 1) :
    |Real.cos (2*(k:ℝ)*Real.pi + sgn*(Real.pi/2+a*(Real.pi/2-Real.arccos r)))| < r := by
  have hp : 0 < Real.arccos r := Real.arccos_pos.mpr hr1
  have hhalf : Real.arccos r < Real.pi/2 := Real.arccos_lt_pi_div_two.mpr hr
  have he : 2*(k:ℝ)*Real.pi + sgn*(Real.pi/2+a*(Real.pi/2-Real.arccos r)) =
      sgn*(Real.pi/2+a*(Real.pi/2-Real.arccos r)) + (k:ℝ)*(2*Real.pi) := by ring
  rw [he,Real.cos_add_int_mul_two_pi,cos_sign_mul _ _ hs]
  have ha₁ := (abs_lt.mp ha).1
  have ha₂ := (abs_lt.mp ha).2
  have hl : Real.arccos r < Real.pi/2+a*(Real.pi/2-Real.arccos r) := by nlinarith
  have hu : Real.pi/2+a*(Real.pi/2-Real.arccos r) < Real.pi-Real.arccos r := by nlinarith
  have h₁ := Real.cos_lt_cos_of_nonneg_of_le_pi (Real.arccos_nonneg r)
    (show Real.pi/2+a*(Real.pi/2-Real.arccos r) ≤ Real.pi by linarith) hl
  have h₂ := Real.cos_lt_cos_of_nonneg_of_le_pi
    (show 0 ≤ Real.pi/2+a*(Real.pi/2-Real.arccos r) by linarith)
    (show Real.pi-Real.arccos r ≤ Real.pi by linarith) hu
  rw [Real.cos_pi_sub,Real.cos_arccos (by linarith) hr1.le] at h₂
  rw [Real.cos_arccos (by linarith) hr1.le] at h₁
  exact abs_lt.mpr ⟨h₂,h₁⟩

end
end IsingBulk.Joint
