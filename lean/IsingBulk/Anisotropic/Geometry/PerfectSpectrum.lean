import IsingBulk.Anisotropic.Geometry.PuncturedTopology
import IsingBulk.Anisotropic.Geometry.ClosedSpectralSet

namespace IsingBulk.Anisotropic
noncomputable section
open scoped Topology

theorem curve_accPt {g : ℝ→ℂ} (hg : Continuous g) (hi : Function.Injective g)
    {s : Set ℂ} (hm : ∀y,g y∈s) (a : ℝ) : AccPt (g a) (Filter.principal s) := by
  rw [accPt_principal_iff_clusterPt,←mem_closure_iff_clusterPt]
  have hf : LocallyFiniteSubset {g a} := fun z =>
    ⟨Set.univ,isOpen_univ,Set.mem_univ z,(Set.finite_singleton (g a)).inter_of_left _⟩
  exact curve_closure_subset_closure_diff hf hg hi isOpen_univ (fun y _ => hm y)
    ⟨a,by simp,rfl⟩

theorem real_eq_inverse_or_neg_of_F2_zero {lam : ℝ} (hlam : 0<lam) {x y : ℝ}
    (hf : geometryF2 lam x y=0) :
    x=sliceQInv lam (Real.cos (lam*y)) ∨ x= -sliceQInv lam (Real.cos (lam*y)) := by
  rw [geometryF2_factor] at hf
  have he := (mul_eq_zero.mp hf).resolve_left (sq_pos_of_pos (Real.cosh_pos x)).ne'
  have hs : sliceQ lam x^2=Real.cos (lam*y)^2 := by linarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h
  · left
    rw [←h,sliceQ_inv_apply hlam]
  · right
    have hn : Real.cos (lam*y)=sliceQ lam (-x) := by rw [sliceQ_neg,h,neg_neg]
    rw [hn,sliceQ_inv_apply hlam,neg_neg]

theorem graph_accPt {f : ℝ→ℝ} (hf : Continuous f) {s : Set ℂ}
    (hm : ∀y,(f y:ℂ)+(y:ℂ)*Complex.I∈s) {z : ℂ} (hz : z.re=f z.im) :
    AccPt z (Filter.principal s) := by
  let g : ℝ→ℂ := fun y => (f y:ℂ)+(y:ℂ)*Complex.I
  have hg : Continuous g := (Complex.continuous_ofReal.comp hf).add
    (Complex.continuous_ofReal.mul_const Complex.I)
  have hi : Function.Injective g := by
    intro a b h
    simpa [g] using congrArg Complex.im h
  have he : g z.im=z := by
    apply Complex.ext
    · simpa [g] using hz.symm
    · simp [g]
  rw [←he]
  exact curve_accPt hg hi hm z.im

theorem spectral_accPt_of_F1_zero {lam : ℝ} (hlam : 0<lam) {z : ℂ}
    (hf : geometryF1 lam z.re z.im=0) : AccPt z (Filter.principal (spectralSet lam)) := by
  rcases real_eq_inverse_or_neg_of_F1_zero hlam hf with h | h
  · apply graph_accPt ((slicePInv_continuous hlam).comp Real.continuous_cos) _ h
    intro y
    apply (mem_spectralSet_iff_signs hlam _).mpr
    simp only [Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,
      sub_zero,add_zero,zero_add]
    simp only [Function.comp_apply]
    rw [geometryF1_factor,sliceP_apply_inv hlam,sub_self,mul_zero,zero_mul]
  · apply graph_accPt (((slicePInv_continuous hlam).comp Real.continuous_cos).neg) _ h
    intro y
    apply (mem_spectralSet_iff_signs hlam _).mpr
    simp only [Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,
      sub_zero,add_zero,zero_add]
    simp only [Function.comp_apply,Pi.neg_apply]
    rw [geometryF1_factor,sliceP_neg,sliceP_apply_inv hlam,neg_sq,sub_self,mul_zero,zero_mul]

theorem spectral_accPt_of_F2_zero {lam : ℝ} (hlam : 0<lam) {z : ℂ}
    (hf : geometryF2 lam z.re z.im=0) : AccPt z (Filter.principal (spectralSet lam)) := by
  have hc : Continuous (fun y : ℝ => Real.cos (lam*y)) := Real.continuous_cos.comp (continuous_const.mul continuous_id)
  rcases real_eq_inverse_or_neg_of_F2_zero hlam hf with h | h
  · apply graph_accPt ((sliceQInv_continuous hlam).comp hc) _ h
    intro y
    apply (mem_spectralSet_iff_signs hlam _).mpr
    simp only [Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,
      sub_zero,add_zero,zero_add]
    simp only [Function.comp_apply]
    rw [geometryF2_factor,sliceQ_apply_inv hlam,sub_self,mul_zero,mul_zero]
  · apply graph_accPt (((sliceQInv_continuous hlam).comp hc).neg) _ h
    intro y
    apply (mem_spectralSet_iff_signs hlam _).mpr
    simp only [Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,
      sub_zero,add_zero,zero_add]
    simp only [Function.comp_apply,Pi.neg_apply]
    rw [geometryF2_factor,sliceQ_neg,sliceQ_apply_inv hlam,neg_sq,sub_self,mul_zero,mul_zero]

/-- The full spectral set has no isolated points, including all degenerate contacts. -/
theorem spectralSet_preperfect {lam : ℝ} (hlam : 0<lam) : Preperfect (spectralSet lam) := by
  intro z hz
  have hp := (mem_spectralSet_iff_signs hlam z).mp hz
  by_cases he : geometryF1 lam z.re z.im*geometryF2 lam z.re z.im=0
  · rcases mul_eq_zero.mp he with h | h
    · exact spectral_accPt_of_F1_zero hlam h
    · exact spectral_accPt_of_F2_zero hlam h
  · let V : Set ℂ := {w | geometryF1 lam w.re w.im*geometryF2 lam w.re w.im<0}
    have ho : IsOpen V := isOpen_lt ((geometryF1_continuous lam).mul (geometryF2_continuous lam)) continuous_const
    have hzV : z∈V := lt_of_le_of_ne hp he
    have hm : V⊆spectralSet lam := fun w hw => (mem_spectralSet_iff_signs hlam w).mpr hw.le
    exact (ho.preperfect z hzV).mono (Filter.principal_mono.mpr hm)

theorem spectralSet_perfect {lam : ℝ} (hlam : 0<lam) : Perfect (spectralSet lam) :=
  ⟨spectralSet_isClosed lam,spectralSet_preperfect hlam⟩

end
end IsingBulk.Anisotropic
