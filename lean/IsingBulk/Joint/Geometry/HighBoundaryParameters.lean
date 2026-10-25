import IsingBulk.Joint.Geometry.HighFaceParameter

namespace IsingBulk.Joint
noncomputable section
open Set

theorem realProduct_le_one_of_closure_high {K : Coupling} (hK : K ∈ closure highDomain) :
    realProduct (K.1.re,K.2.re) ≤ 1 := by
  have hg := (closure_high_inequalities hK).1
  have hr : faceRatio1 (K.1.re,K.2.re) ≤ 1 := hg.trans (Real.cos_le_one _)
  by_contra h
  have hp : 1 < realProduct (K.1.re,K.2.re) := lt_of_not_ge h
  have he := (real_edge_low_iff (abs_nonneg K.1.re) (abs_nonneg K.2.re)).mpr hp
  rw [cosh_abs_eq] at he
  exact (not_lt_of_ge hr) he

theorem high_boundary_active_face {K : Coupling} (hK : K ∈ frontier highDomain) :
    faceRatio1 (K.1.re,K.2.re) = Real.cos K.1.im ∨
    faceRatio2 (K.1.re,K.2.re) = Real.cos K.2.im := by
  have hc := frontier_subset_closure hK
  obtain ⟨hy,hv,_,_⟩ := closure_high_bounds hc
  obtain ⟨h₁,h₂⟩ := closure_high_inequalities hc
  by_contra h
  push Not at h
  have hg₁ := lt_of_le_of_ne h₁ h.1
  have hg₂ := lt_of_le_of_ne h₂ h.2
  have hnonneg (x u : ℝ) : 0 ≤ Real.cosh x * Real.tanh |u| := by
    have ht : 0 ≤ Real.tanh |u| := by
      simpa using IsingBulk.Anisotropic.tanh_strictMono.monotone (abs_nonneg u)
    exact mul_nonneg (Real.cosh_pos x).le ht
  have hy' : |K.1.im| < Real.pi/2 := by
    apply lt_of_le_of_ne hy
    intro he
    have hh : Real.cos K.1.im = 0 := by rw [←Real.cos_abs,he,Real.cos_pi_div_two]
    rw [hh] at hg₁
    exact (not_lt_of_ge (hnonneg _ _)) hg₁
  have hv' : |K.2.im| < Real.pi/2 := by
    apply lt_of_le_of_ne hv
    intro he
    have hh : Real.cos K.2.im = 0 := by rw [←Real.cos_abs,he,Real.cos_pi_div_two]
    rw [hh] at hg₂
    exact (not_lt_of_ge (hnonneg _ _)) hg₂
  rw [highDomain_isOpen.frontier_eq] at hK
  exact hK.2 ⟨hy',hv',hg₁,hg₂⟩

theorem high_first_face_parameter_exists {K : Coupling} (hK : K ∈ closure highDomain)
    (hface : faceRatio1 (K.1.re,K.2.re) = Real.cos K.1.im) :
    ∃ sgn a : ℝ, (sgn = -1 ∨ sgn = 1) ∧ |a| ≤ 1 ∧
      highFaceParameter sgn ((K.1.re,K.2.re),a) = K := by
  obtain ⟨hy,hv,_,_⟩ := closure_high_bounds hK
  have hg₂ := (closure_high_inequalities hK).2
  have hac : Real.arccos (faceRatio1 (K.1.re,K.2.re)) = |K.1.im| := by
    rw [hface,←Real.cos_abs,Real.arccos_cos (abs_nonneg _) (by linarith [Real.pi_pos])]
  have hac₂ : |K.2.im| ≤ Real.arccos (faceRatio2 (K.1.re,K.2.re)) := by
    have he := Real.arccos_le_arccos hg₂
    rw [←Real.cos_abs K.2.im,Real.arccos_cos (abs_nonneg _) (by linarith [Real.pi_pos])] at he
    exact he
  obtain ⟨a,ha,hea⟩ : ∃ a : ℝ, |a| ≤ 1 ∧
      a*Real.arccos (faceRatio2 (K.1.re,K.2.re)) = K.2.im := by
    let R := Real.arccos (faceRatio2 (K.1.re,K.2.re))
    by_cases hR : R = 0
    · have hz : K.2.im = 0 := by change |K.2.im| ≤ R at hac₂; rw [hR] at hac₂; exact abs_nonpos_iff.mp hac₂
      exact ⟨0,by norm_num,by simp [hz]⟩
    · have hRpos : 0 < R := lt_of_le_of_ne (Real.arccos_nonneg _) (Ne.symm hR)
      refine ⟨K.2.im/R,?_,?_⟩
      · rw [abs_div,abs_of_pos hRpos,div_le_one hRpos]
        exact hac₂
      · exact div_mul_cancel₀ _ hR
  let sgn : ℝ := if K.1.im < 0 then -1 else 1
  have hs : sgn = -1 ∨ sgn = 1 := by dsimp [sgn]; split_ifs <;> simp
  have hes : sgn*Real.arccos (faceRatio1 (K.1.re,K.2.re)) = K.1.im := by
    rw [hac]
    dsimp [sgn]
    split_ifs with h
    · rw [abs_of_neg h]; ring
    · rw [abs_of_nonneg (le_of_not_gt h),one_mul]
  refine ⟨sgn,a,hs,ha,?_⟩
  apply Prod.ext <;> apply Complex.ext <;> simp [highFaceParameter,hes,hea]

end
end IsingBulk.Joint
