import IsingBulk.Anisotropic.Geometry.ComponentDensity

namespace IsingBulk.Anisotropic
noncomputable section

theorem edgeV_numerator_relation (h c H C t q T Q e : ℝ) (he : e^2=1) (hr : C*t=e*c*H) :
    h*c*H*Q-C*t*q*T=e*(h*C*t*Q-c*H*q*T) := by
  linear_combination -(e*h*Q+q*T)*hr-h*Q*c*H*he

theorem edgeU_numerator_relation (h c H C t q T Q e : ℝ) (he : e^2=1) (hr : c*T=e*h*C) :
    c*t*T*Q-h*H*C*q=e*(h*C*t*Q-c*H*q*T) := by
  linear_combination (t*Q+e*H*q)*hr+H*q*h*C*he

theorem spectralV_eq_of_edge_relation {lam : ℝ} {z : ℂ} {e : ℝ}
    (hd : spectralDet lam z≠0) (he : e^2=1)
    (hr : Real.cosh (lam*z.re)*Real.cos z.im=e*Real.cosh z.re*Real.sinh (lam*z.re)) :
    spectralV lam z=e := by
  apply (div_eq_iff hd).mpr
  rw [spectralNV_formula,spectralDet_formula]
  exact edgeV_numerator_relation _ _ _ _ _ _ _ _ _ he hr

theorem spectralU_eq_of_edge_relation {lam : ℝ} {z : ℂ} {e : ℝ}
    (hd : spectralDet lam z≠0) (he : e^2=1)
    (hr : Real.cosh z.re*Real.cos (lam*z.im)=e*Real.sinh z.re*Real.cosh (lam*z.re)) :
    spectralU lam z=e := by
  apply (div_eq_iff hd).mpr
  rw [spectralNU_formula,spectralDet_formula]
  exact edgeU_numerator_relation _ _ _ _ _ _ _ _ _ he hr

/-- On a right-half-plane F1 edge the endpoint V has precisely the sign of cos y. -/
theorem spectralV_sign_of_F1_zero {lam : ℝ} (hlam : 0<lam) {z : ℂ}
    (hx : 0<z.re) (hd : spectralDet lam z≠0) (hf : geometryF1 lam z.re z.im=0) :
    (0<Real.cos z.im ∧ spectralV lam z=1) ∨ (Real.cos z.im<0 ∧ spectralV lam z= -1) := by
  have hc := Real.cosh_pos z.re
  have hC := Real.cosh_pos (lam*z.re)
  have hH := Real.sinh_pos_iff.mpr (mul_pos hlam hx)
  have hs : (Real.cosh (lam*z.re)*Real.cos z.im)^2=(Real.cosh z.re*Real.sinh (lam*z.re))^2 := by
    unfold geometryF1 at hf
    nlinarith [hf]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h
  · refine Or.inl ⟨?_,spectralV_eq_of_edge_relation hd (by norm_num) (by simpa using h)⟩
    exact pos_of_mul_pos_right (h.symm ▸ mul_pos hc hH) hC.le
  · refine Or.inr ⟨?_,spectralV_eq_of_edge_relation hd (by norm_num) (by simpa using h)⟩
    have hn : Real.cosh (lam*z.re)*Real.cos z.im<0 := by rw [h]; exact neg_neg_of_pos (mul_pos hc hH)
    exact neg_of_mul_neg_right hn hC.le

/-- On a right-half-plane F2 edge the endpoint U has precisely the sign of cos(λy). -/
theorem spectralU_sign_of_F2_zero {lam : ℝ} {z : ℂ}
    (hx : 0<z.re) (hd : spectralDet lam z≠0) (hf : geometryF2 lam z.re z.im=0) :
    (0<Real.cos (lam*z.im) ∧ spectralU lam z=1) ∨ (Real.cos (lam*z.im)<0 ∧ spectralU lam z= -1) := by
  have hc := Real.cosh_pos z.re
  have hC := Real.cosh_pos (lam*z.re)
  have hh := Real.sinh_pos_iff.mpr hx
  have hs : (Real.cosh z.re*Real.cos (lam*z.im))^2=(Real.sinh z.re*Real.cosh (lam*z.re))^2 := by
    unfold geometryF2 at hf
    nlinarith [hf]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h
  · refine Or.inl ⟨?_,spectralU_eq_of_edge_relation hd (by norm_num) (by simpa using h)⟩
    exact pos_of_mul_pos_right (h.symm ▸ mul_pos hh hC) hc.le
  · refine Or.inr ⟨?_,spectralU_eq_of_edge_relation hd (by norm_num) (by simpa using h)⟩
    have hn : Real.cosh z.re*Real.cos (lam*z.im)<0 := by rw [h]; exact neg_neg_of_pos (mul_pos hh hC)
    exact neg_of_mul_neg_right hn hc.le


theorem spectralU_neg (lam : ℝ) (z : ℂ) : spectralU lam (-z)= -spectralU lam z := by
  simp [spectralU,spectralNU,spectralDet,spectralS,spectralT,spectralA,mul_neg,
    Complex.sinh_neg,Complex.cosh_neg,Complex.neg_re,Complex.neg_im]
  ring

theorem spectralV_neg (lam : ℝ) (z : ℂ) : spectralV lam (-z)= -spectralV lam z := by
  simp [spectralV,spectralNV,spectralDet,spectralS,spectralT,spectralA,mul_neg,
    Complex.sinh_neg,Complex.cosh_neg,Complex.neg_re,Complex.neg_im]
  ring

theorem spectralDet_neg (lam : ℝ) (z : ℂ) : spectralDet lam (-z)=spectralDet lam z := by
  simp [spectralDet,spectralS,spectralT,mul_neg,Complex.sinh_neg,Complex.neg_re,Complex.neg_im]

/-- The right high-temperature frontier has only positive endpoints. -/
theorem frontier_omegaH_right_positive_endpoint {lam : ℝ} (hlam : 0<lam) {z : ℂ}
    (hz : z∈frontier (omegaH lam)) (hx : 0<z.re) (hd : spectralDet lam z≠0) :
    spectralU lam z=1 ∨ spectralV lam z=1 := by
  have hb := (mem_frontier_omegaH_iff hlam z).mp hz
  have hy : |z.im|<sliceY lam := lt_of_le_of_ne hb.1 (by
    intro heq
    rw [sliceH_zero_at_endpoint hlam heq] at hb
    have := (abs_eq_zero.mp hb.2)
    linarith)
  have hc := central_strip_bounds hlam hy
  have hc1 := Real.cos_pos_of_mem_Ioo (abs_lt.mp hc.1)
  have hc2 := Real.cos_pos_of_mem_Ioo (abs_lt.mp hc.2)
  have hf := closure_omegaH_bounds hlam (frontier_subset_closure hz)
  have hp := (mem_spectralSet_iff_signs hlam z).mp (frontier_omegaH_subset_spectralSet hlam hz)
  have heq : geometryF1 lam z.re z.im*geometryF2 lam z.re z.im=0 :=
    le_antisymm hp (mul_nonneg hf.2.1 hf.2.2)
  rcases mul_eq_zero.mp heq with h | h
  · rcases spectralV_sign_of_F1_zero hlam hx hd h with h | h
    · exact Or.inr h.2
    · linarith [h.1]
  · rcases spectralU_sign_of_F2_zero hx hd h with h | h
    · exact Or.inl h.2
    · linarith [h.1]

/-- The left high-temperature frontier has only negative endpoints. -/
theorem frontier_omegaH_left_negative_endpoint {lam : ℝ} (hlam : 0<lam) {z : ℂ}
    (hz : z∈frontier (omegaH lam)) (hx : z.re<0) (hd : spectralDet lam z≠0) :
    spectralU lam z= -1 ∨ spectralV lam z= -1 := by
  have hnz : -z∈frontier (omegaH lam) := by
    rw [mem_frontier_omegaH_iff hlam] at hz ⊢
    simpa only [Complex.neg_re,Complex.neg_im,abs_neg,sliceH,mul_neg,Real.cos_neg] using hz
  have h := frontier_omegaH_right_positive_endpoint hlam hnz (by simpa using neg_pos.mpr hx)
    (by simpa only [spectralDet_neg] using hd)
  simp only [spectralU_neg,spectralV_neg,neg_eq_iff_eq_neg] at h
  exact h

end
end IsingBulk.Anisotropic
