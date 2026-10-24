import IsingBulk.Anisotropic.Geometry.ExactSpectralSet
import IsingBulk.Anisotropic.Geometry.BoundaryProfiles

namespace IsingBulk.Anisotropic
noncomputable section

theorem geometryF1_continuous (lam : ℝ) : Continuous (fun z : ℂ => geometryF1 lam z.re z.im) := by
  unfold geometryF1
  fun_prop

theorem geometryF2_continuous (lam : ℝ) : Continuous (fun z : ℂ => geometryF2 lam z.re z.im) := by
  unfold geometryF2
  fun_prop

theorem geometryF1_zero_at_inverse {lam : ℝ} (hlam : 0<lam) (y : ℝ) :
    geometryF1 lam (slicePInv lam |Real.cos y|) y=0 := by
  rw [geometryF1_factor,sliceP_apply_inv hlam,sq_abs,sub_self,mul_zero]

theorem geometryF2_zero_at_inverse {lam : ℝ} (hlam : 0<lam) (y : ℝ) :
    geometryF2 lam (sliceQInv lam |Real.cos (lam*y)|) y=0 := by
  rw [geometryF2_factor,sliceQ_apply_inv hlam,sq_abs,sub_self,mul_zero]

theorem frontier_omegaL_subset_spectralSet {lam : ℝ} (hlam : 0<lam) :
    frontier (omegaL lam) ⊆ spectralSet lam := by
  intro z hz
  apply (mem_spectralSet_iff_signs hlam z).mpr
  rw [(mem_frontier_omegaL_iff hlam z).mp hz]
  unfold sliceL
  rcases le_total (slicePInv lam |Real.cos z.im|) (sliceQInv lam |Real.cos (lam*z.im)|) with h | h
  · rw [max_eq_right h,geometryF2_zero_at_inverse hlam,mul_zero]
  · rw [max_eq_left h,geometryF1_zero_at_inverse hlam,zero_mul]

theorem closure_omegaH_bounds {lam : ℝ} (hlam : 0<lam) {z : ℂ} (hz : z∈closure (omegaH lam)) :
    |z.im|≤sliceY lam ∧ 0≤geometryF1 lam z.re z.im ∧ 0≤geometryF2 lam z.re z.im := by
  have hstrip : closure (omegaH lam) ⊆ {z : ℂ | |z.im|≤sliceY lam} := by
    apply closure_minimal
    · intro z hz
      exact hz.1.le
    · exact isClosed_le (Complex.continuous_im.abs) continuous_const
  have hf1 : closure (omegaH lam) ⊆ {z : ℂ | 0≤geometryF1 lam z.re z.im} := by
    apply closure_minimal
    · intro z hz
      exact (positive_signs_of_mem_omegaH hlam hz).1.le
    · exact isClosed_le continuous_const (geometryF1_continuous lam)
  have hf2 : closure (omegaH lam) ⊆ {z : ℂ | 0≤geometryF2 lam z.re z.im} := by
    apply closure_minimal
    · intro z hz
      exact (positive_signs_of_mem_omegaH hlam hz).2.le
    · exact isClosed_le continuous_const (geometryF2_continuous lam)
  exact ⟨hstrip hz,hf1 hz,hf2 hz⟩

theorem strip_endpoint_cos_zero {lam : ℝ} (hlam : 0<lam) {y : ℝ} (hy : |y|=sliceY lam) :
    Real.cos y=0 ∨ Real.cos (lam*y)=0 := by
  by_cases hl : lam≤1
  · left
    rw [← Real.cos_abs,hy]
    simp [sliceY,max_eq_left hl]
  · right
    have hly : |lam*y|=Real.pi/2 := by
      rw [abs_mul,abs_of_pos hlam,hy]
      unfold sliceY
      rw [max_eq_right (le_of_not_ge hl)]
      field_simp
    rw [← Real.cos_abs,hly,Real.cos_pi_div_two]

theorem mem_omegaH_of_positive_signs {lam : ℝ} (hlam : 0<lam) {z : ℂ}
    (hy : |z.im|<sliceY lam)
    (hf : 0<geometryF1 lam z.re z.im) (hg : 0<geometryF2 lam z.re z.im) : z∈omegaH lam := by
  refine ⟨hy,?_⟩
  have hb := central_strip_bounds hlam hy
  have hc := Real.cos_pos_of_mem_Ioo (abs_lt.mp hb.1)
  have hC := Real.cos_pos_of_mem_Ioo (abs_lt.mp hb.2)
  have h1 := (geometryF1_pos_iff hlam (abs_nonneg z.re) z.im).mp
    (by simpa only [geometryF1_abs] using hf)
  have h2 := (geometryF2_pos_iff hlam (abs_nonneg z.re) z.im).mp
    (by simpa only [geometryF2_abs] using hg)
  exact lt_min (by simpa only [abs_of_pos hc] using h1) (by simpa only [abs_of_pos hC] using h2)

theorem frontier_omegaH_subset_spectralSet {lam : ℝ} (hlam : 0<lam) :
    frontier (omegaH lam) ⊆ spectralSet lam := by
  intro z hz
  by_contra hs
  have hb := closure_omegaH_bounds hlam (frontier_subset_closure hz)
  have hp : 0<geometryF1 lam z.re z.im*geometryF2 lam z.re z.im :=
    lt_of_not_ge (fun h => hs ((mem_spectralSet_iff_signs hlam z).mpr h))
  have hf : 0<geometryF1 lam z.re z.im := lt_of_le_of_ne hb.2.1 (by
    intro h
    rw [← h,zero_mul] at hp
    exact (lt_irrefl _ hp))
  have hg : 0<geometryF2 lam z.re z.im := lt_of_le_of_ne hb.2.2 (by
    intro h
    rw [← h,mul_zero] at hp
    exact (lt_irrefl _ hp))
  have hy : |z.im|<sliceY lam := lt_of_le_of_ne hb.1 (by
    intro he
    rcases strip_endpoint_cos_zero hlam he with hcos | hcos
    · simp only [geometryF1,hcos,zero_pow (by decide : 2≠0),mul_zero,zero_sub] at hf
      nlinarith [mul_nonneg (sq_nonneg (Real.cosh z.re)) (sq_nonneg (Real.sinh (lam*z.re)))]
    · simp only [geometryF2,hcos,zero_pow (by decide : 2≠0),mul_zero,zero_sub] at hg
      nlinarith [mul_nonneg (sq_nonneg (Real.sinh z.re)) (sq_nonneg (Real.cosh (lam*z.re)))])
  rw [(omegaH_isOpen hlam).frontier_eq] at hz
  exact hz.2 (mem_omegaH_of_positive_signs hlam hy hf hg)

end
end IsingBulk.Anisotropic
