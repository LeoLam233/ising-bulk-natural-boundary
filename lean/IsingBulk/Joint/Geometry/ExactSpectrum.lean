import IsingBulk.Joint.Geometry.SpectralComplement

namespace IsingBulk.Joint
noncomputable section

private theorem axis_rectangle (H C t q V Q : ℝ)
    (hH : 0<H) (hC : 0<C) (hHC : C^2-H^2=1)
    (ht : q^2+t^2=1) (hV : Q^2+V^2=1)
    (hf : (C^2*t^2-H^2)*V^2≤0) :
    ∃ a∈Set.Icc (-1:ℝ) 1, ∃ b∈Set.Icc (-1:ℝ) 1,
      C*t*V=H*V*b ∧ H*t*Q=q*a+C*Q*b := by
  have ht1 : t^2≤1 := by nlinarith [sq_nonneg q]
  by_cases hv : V=0
  · let b := H*t/C
    have hb : b^2≤1 := by
      dsimp [b]
      rw [div_pow,div_le_one₀ (sq_pos_of_pos hC),mul_pow]
      nlinarith [mul_nonneg (sq_nonneg H) (sub_nonneg.mpr ht1)]
    refine ⟨0,by norm_num,b,abs_le.mp ((sq_le_one_iff_abs_le_one b).mp hb),?_⟩
    constructor
    · simp [hv]
    · dsimp [b]; field_simp; ring
  · have hineq : C^2*t^2≤H^2 := by
      have h := nonpos_of_mul_nonpos_left hf (sq_pos_of_ne_zero hv)
      linarith
    have hq : q≠0 := by
      intro he
      rw [he] at ht
      nlinarith
    let a := -(t*Q)/(H*q)
    let b := C*t/H
    have hb : b^2≤1 := by
      dsimp [b]
      rw [div_pow,div_le_one₀ (sq_pos_of_pos hH),mul_pow]
      exact hineq
    have ha : a^2≤1 := by
      dsimp [a]
      rw [div_pow,div_le_one₀ (sq_pos_of_ne_zero (mul_ne_zero hH.ne' hq)),neg_sq,mul_pow,mul_pow]
      nlinarith [mul_nonneg (sq_nonneg t) (sq_nonneg V)]
    refine ⟨a,abs_le.mp ((sq_le_one_iff_abs_le_one a).mp ha),
      b,abs_le.mp ((sq_le_one_iff_abs_le_one b).mp hb),?_⟩
    constructor
    · dsimp [b]; field_simp
    · dsimp [a,b]
      field_simp
      linear_combination -t*Q*hHC

theorem mem_spectralSet_of_zero_first_real {K : Coupling}
    (hx : K.1.re=0) (hu : 0≤K.2.re) (hf : F1 K*F2 K≤0) : K∈spectralSet := by
  rcases eq_or_lt_of_le hu with hu|hu
  · have hp : Real.cos K.1.im*Real.cos K.2.im=0 := by
      have hh : (Real.cos K.1.im*Real.cos K.2.im)^2≤0 := by
        simpa [F1,F2,hx,hu.symm,mul_pow] using hf
      nlinarith [sq_nonneg (Real.cos K.1.im*Real.cos K.2.im)]
    refine ⟨0,by norm_num,0,by norm_num,?_⟩
    simp only [Complex.ofReal_zero,mul_zero,add_zero]
    apply Complex.ext
    · simpa [A_re,hx,hu.symm] using hp
    · simp [A_im,hx,hu.symm]
  · have hf' : (Real.cosh K.2.re^2*Real.cos K.1.im^2-Real.sinh K.2.re^2)*Real.cos K.2.im^2≤0 := by
      simpa [F1,F2,hx] using hf
    rcases axis_rectangle (Real.sinh K.2.re) (Real.cosh K.2.re)
      (Real.cos K.1.im) (Real.sin K.1.im) (Real.cos K.2.im) (Real.sin K.2.im)
      (Real.sinh_pos_iff.mpr hu) (Real.cosh_pos _) (Real.cosh_sq_sub_sinh_sq _)
      (Real.sin_sq_add_cos_sq _) (Real.sin_sq_add_cos_sq _) hf' with ⟨a,ha,b,hb,hr,hi⟩
    refine ⟨a,ha,b,hb,?_⟩
    apply Complex.ext
    · simpa [A_re,S_re,T_re,Complex.add_re,Complex.mul_re,hx] using hr
    · simpa [A_im,S_im,T_im,Complex.add_im,Complex.mul_im,hx,mul_comm,mul_left_comm,mul_assoc] using hi

theorem mem_spectralSet_iff_signs_nonnegative_quadrant {K : Coupling}
    (hx : 0≤K.1.re) (hu : 0≤K.2.re) : K∈spectralSet ↔ F1 K*F2 K≤0 := by
  constructor
  · exact signs_of_mem_spectralSet
  · intro hf
    rcases eq_or_lt_of_le hx with hx|hx
    · exact mem_spectralSet_of_zero_first_real hx.symm hu hf
    rcases eq_or_lt_of_le hu with hu|hu
    · apply (swap_mem_spectralSet_iff K).mp
      exact mem_spectralSet_of_zero_first_real (K := K.swap) hu.symm hx.le (by simpa [mul_comm] using hf)
    · exact (mem_spectralSet_iff_signs_positive_quadrant hx hu).mpr hf

/-- JOINT Theorem 2.1: the exact unsquared spectrum, with no real-part or collinearity exclusion. -/
theorem mem_spectralSet_iff_signs (K : Coupling) : K∈spectralSet ↔ F1 K*F2 K≤0 := by
  constructor
  · exact signs_of_mem_spectralSet
  · intro hf
    rcases le_or_gt 0 K.1.re with hx|hx
    · rcases le_or_gt 0 K.2.re with hu|hu
      · exact (mem_spectralSet_iff_signs_nonnegative_quadrant hx hu).mpr hf
      · apply (reflectY_mem_spectralSet_iff K).mp
        apply (mem_spectralSet_iff_signs_nonnegative_quadrant (K := reflectY K) hx
          (by simpa [reflectY] using (neg_pos.mpr hu).le)).mpr
        simpa using hf
    · rcases le_or_gt 0 K.2.re with hu|hu
      · apply (reflectX_mem_spectralSet_iff K).mp
        apply (mem_spectralSet_iff_signs_nonnegative_quadrant (K := reflectX K)
          (by simpa [reflectX] using (neg_pos.mpr hx).le) hu).mpr
        simpa using hf
      · apply (reflectY_mem_spectralSet_iff K).mp
        apply (reflectX_mem_spectralSet_iff (reflectY K)).mp
        apply (mem_spectralSet_iff_signs_nonnegative_quadrant (K := reflectX (reflectY K))
          (by simpa [reflectX,reflectY] using (neg_pos.mpr hx).le)
          (by simpa [reflectX,reflectY] using (neg_pos.mpr hu).le)).mpr
        simpa using hf

theorem spectralSet_eq_signs : spectralSet = {K | F1 K*F2 K≤0} := by
  ext K
  exact mem_spectralSet_iff_signs K

end
end IsingBulk.Joint
