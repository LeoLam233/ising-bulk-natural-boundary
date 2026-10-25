import IsingBulk.Joint.Geometry.PositiveQuadrant

namespace IsingBulk.Joint
noncomputable section

def reflectX (K : Coupling) : Coupling := (-K.1,K.2)
def reflectY (K : Coupling) : Coupling := (K.1,-K.2)

@[simp] theorem F1_reflectX (K : Coupling) : F1 (reflectX K)=F1 K := by simp [F1,reflectX]
@[simp] theorem F2_reflectX (K : Coupling) : F2 (reflectX K)=F2 K := by simp [F2,reflectX]
@[simp] theorem F1_reflectY (K : Coupling) : F1 (reflectY K)=F1 K := by simp [F1,reflectY]
@[simp] theorem F2_reflectY (K : Coupling) : F2 (reflectY K)=F2 K := by simp [F2,reflectY]
@[simp] theorem F1_swap (K : Coupling) : F1 K.swap=F2 K := by simp [F1,F2,mul_comm]
@[simp] theorem F2_swap (K : Coupling) : F2 K.swap=F1 K := by simp [F1,F2,mul_comm]

theorem reflectX_mem_spectralSet_iff (K : Coupling) : reflectX K∈spectralSet ↔ K∈spectralSet := by
  constructor <;> rintro ⟨a,ha,b,hb,h⟩
  · exact ⟨-a,⟨by linarith [ha.2],by linarith [ha.1]⟩,b,hb,
      by simpa [A,S,T,reflectX] using h⟩
  · exact ⟨-a,⟨by linarith [ha.2],by linarith [ha.1]⟩,b,hb,
      by simpa [A,S,T,reflectX] using h⟩

theorem reflectY_mem_spectralSet_iff (K : Coupling) : reflectY K∈spectralSet ↔ K∈spectralSet := by
  constructor <;> rintro ⟨a,ha,b,hb,h⟩
  · exact ⟨a,ha,-b,⟨by linarith [hb.2],by linarith [hb.1]⟩,
      by simpa [A,S,T,reflectY] using h⟩
  · exact ⟨a,ha,-b,⟨by linarith [hb.2],by linarith [hb.1]⟩,
      by simpa [A,S,T,reflectY] using h⟩

theorem signs_of_mem_zero_first_real {K : Coupling}
    (hx : K.1.re=0) (hK : K∈spectralSet) : F1 K*F2 K≤0 := by
  rcases hK with ⟨a,ha,b,hb,he⟩
  have hre := congrArg Complex.re he
  simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,
    sub_zero,A_re,S_re,T_re,hx,Real.cosh_zero,Real.sinh_zero,one_mul,zero_mul,zero_add] at hre
  by_cases hc : Real.cos K.2.im=0
  · simp [F1,F2,hx,hc]
  · have heq : Real.cosh K.2.re*Real.cos K.1.im=Real.sinh K.2.re*b := by
      apply mul_right_cancel₀ hc
      nlinarith [hre]
    have hb2 := (sq_le_one_iff_abs_le_one b).mpr (abs_le.mpr hb)
    have hsq := congrArg (fun t : ℝ => t^2) heq
    have hineq : Real.cosh K.2.re^2*Real.cos K.1.im^2≤Real.sinh K.2.re^2 := by
      nlinarith [mul_nonneg (sq_nonneg (Real.sinh K.2.re)) (sub_nonneg.mpr hb2)]
    have hF : F1 K≤0 := by simpa [F1,hx] using sub_nonpos.mpr hineq
    have hG : 0≤F2 K := by simp [F2,hx]; positivity
    exact mul_nonpos_of_nonpos_of_nonneg hF hG

theorem signs_of_mem_nonnegative_quadrant {K : Coupling}
    (hx : 0≤K.1.re) (hu : 0≤K.2.re) (hK : K∈spectralSet) : F1 K*F2 K≤0 := by
  rcases eq_or_lt_of_le hx with hx|hx
  · exact signs_of_mem_zero_first_real hx.symm hK
  rcases eq_or_lt_of_le hu with hu|hu
  · have h := signs_of_mem_zero_first_real (K := K.swap) hu.symm ((swap_mem_spectralSet_iff K).mpr hK)
    simpa [mul_comm] using h
  · exact signs_of_mem_positive_quadrant hx hu hK

/-- Necessary spectral signs on all of C², including independent opposite real signs and axes. -/
theorem signs_of_mem_spectralSet {K : Coupling} (hK : K∈spectralSet) : F1 K*F2 K≤0 := by
  rcases le_or_gt 0 K.1.re with hx|hx
  · rcases le_or_gt 0 K.2.re with hu|hu
    · exact signs_of_mem_nonnegative_quadrant hx hu hK
    · have h := signs_of_mem_nonnegative_quadrant (K := reflectY K) hx
        (by simpa [reflectY] using (neg_pos.mpr hu).le) ((reflectY_mem_spectralSet_iff K).mpr hK)
      simpa using h
  · rcases le_or_gt 0 K.2.re with hu|hu
    · have h := signs_of_mem_nonnegative_quadrant (K := reflectX K)
        (by simpa [reflectX] using (neg_pos.mpr hx).le) hu ((reflectX_mem_spectralSet_iff K).mpr hK)
      simpa using h
    · have h := signs_of_mem_nonnegative_quadrant (K := reflectX (reflectY K))
        (by simpa [reflectX,reflectY] using (neg_pos.mpr hx).le)
        (by simpa [reflectX,reflectY] using (neg_pos.mpr hu).le)
        ((reflectX_mem_spectralSet_iff _).mpr ((reflectY_mem_spectralSet_iff K).mpr hK))
      simpa using h

theorem highDomain_subset_spectralComplement : highDomain ⊆ spectralSetᶜ := by
  intro K hK hs
  have h := positive_signs_of_mem_highDomain hK
  exact (not_lt_of_ge (signs_of_mem_spectralSet hs)) (mul_pos h.1 h.2)

theorem lowDomain_subset_spectralComplement : lowDomain ⊆ spectralSetᶜ := by
  intro K hK hs
  have h := negative_signs_of_mem_lowDomain hK
  exact (not_lt_of_ge (signs_of_mem_spectralSet hs)) (mul_pos_of_neg_of_neg h.1 h.2)

end
end IsingBulk.Joint
