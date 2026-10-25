import IsingBulk.Joint.Geometry.ComponentsBoundary
import IsingBulk.Anisotropic.Geometry.RealGeometryAlgebra

namespace IsingBulk.Joint
noncomputable section

/-- Denominator-free regular-face identity, valid for both signs of real parts. -/
theorem face_numerator_identity {K : Coupling} (hf : F1 K = 0) :
    Real.cosh K.2.re^2 * (spectralNU K^2-spectralDet K^2) =
      -Real.sinh K.2.re^2 * F2 K^2 := by
  rw [spectralNU_sq_sub_det_sq]
  have h := (IsingBulk.Anisotropic.edge_auxiliary_identities
    (Real.sinh K.1.re) (Real.cosh K.1.re) (Real.sinh K.2.re) (Real.cosh K.2.re)
    (Real.cos K.1.im) (Real.sin K.1.im) (Real.cos K.2.im) (Real.sin K.2.im)
    (Real.cosh_sq_sub_sinh_sq _) (Real.cosh_sq_sub_sinh_sq _)
    (Real.sin_sq_add_cos_sq _) (Real.sin_sq_add_cos_sq _)).1
  change Real.cosh K.2.re^2 *
    (Real.cos K.1.im^2*Real.sin K.2.im^2-Real.sinh K.2.re^2*Real.sin K.1.im^2) =
    (Real.sinh K.2.re^2+Real.sin K.2.im^2)*F1 K-Real.sinh K.2.re^2*F2 K at h
  rw [hf,mul_zero,zero_sub] at h
  linear_combination F2 K * h

theorem det_ne_zero_of_face {K : Coupling} (hu : K.2.re ≠ 0)
    (hf : F1 K = 0) (hg : F2 K ≠ 0) : spectralDet K ≠ 0 := by
  have he := face_numerator_identity hf
  have hsp : 0 < Real.sinh K.2.re^2 := sq_pos_of_ne_zero (Real.sinh_ne_zero.mpr hu)
  have hfp : 0 < F2 K^2 := sq_pos_of_ne_zero hg
  intro hd
  rw [hd,zero_pow (by decide : 2 ≠ 0),sub_zero] at he
  have hn := mul_nonneg (sq_nonneg (Real.cosh K.2.re)) (sq_nonneg (spectralNU K))
  nlinarith [mul_pos hsp hfp]

theorem strict_free_coordinate_of_face {K : Coupling} (hu : K.2.re ≠ 0)
    (hf : F1 K = 0) (hg : F2 K ≠ 0) : |spectralU K| < 1 := by
  have he := face_numerator_identity hf
  have hsp : 0 < Real.sinh K.2.re^2 := sq_pos_of_ne_zero (Real.sinh_ne_zero.mpr hu)
  have hfp : 0 < F2 K^2 := sq_pos_of_ne_zero hg
  have hd := det_ne_zero_of_face hu hf hg
  rw [spectralU,←sq_lt_one_iff_abs_lt_one,div_pow,div_lt_one (sq_pos_of_ne_zero hd)]
  have hc := sq_pos_of_pos (Real.cosh_pos K.2.re)
  nlinarith [mul_pos hsp hfp]

theorem endpoint_coordinate_of_face {K : Coupling} (hu : K.2.re ≠ 0)
    (hf : F1 K = 0) (hg : F2 K ≠ 0) : spectralV K = -1 ∨ spectralV K = 1 := by
  have hd := det_ne_zero_of_face hu hf hg
  have he := spectralNV_sq_sub_det_sq K
  rw [hf,neg_zero,zero_mul] at he
  have hs : spectralV K^2 = 1 := by
    rw [spectralV,div_pow]
    apply (div_eq_one_iff_eq (pow_ne_zero 2 hd)).mpr
    linarith
  rcases (sq_eq_one_iff).mp hs with h | h
  · exact Or.inr h
  · exact Or.inl h

theorem face_product_identity {K : Coupling} (hf : F1 K = 0) :
    Real.cosh K.2.re^2 * (‖p K‖^2-1) = -F2 K := by
  rw [norm_p_sq]
  have h₁ := Real.cosh_sq_sub_sinh_sq K.1.re
  have h₂ := Real.cosh_sq_sub_sinh_sq K.2.re
  dsimp [F1] at hf
  dsimp [F2]
  linear_combination Real.cosh K.1.re^2*(Real.cosh K.2.re^2-Real.cos K.2.im^2)*h₂ -
    (Real.cosh K.2.re^2-Real.cos K.2.im^2)*hf + Real.cosh K.2.re^2*h₁

theorem regularJointEdge_of_face {K : Coupling}
    (hb : K ∈ frontier highDomain ∪ frontier lowDomain)
    (hu : K.2.re ≠ 0) (hf : F1 K = 0) (hg : F2 K ≠ 0) : IsRegularJointEdge K := by
  have hd := det_ne_zero_of_face hu hf hg
  have hS : S K ≠ 0 := by
    intro h
    apply hd
    simp [spectralDet,h]
  have hT : T K ≠ 0 := by
    intro h
    apply hd
    simp [spectralDet,h]
  have hp : p K^2 ≠ 1 := by
    intro h
    have hn : ‖p K‖^2 = 1 := by simpa only [norm_pow,norm_one] using congrArg norm h
    have he := face_product_identity hf
    rw [hn,sub_self,mul_zero] at he
    exact hg (neg_eq_zero.mp he.symm)
  have hfree := strict_free_coordinate_of_face hu hf hg
  have hend := endpoint_coordinate_of_face hu hf hg
  have hbound : spectralV K ∈ Set.Icc (-1:ℝ) 1 := by rcases hend with h | h <;> simp [h]
  refine ⟨hb,hS,hT,?_,hp,spectralU K,(abs_le.mp hfree.le),spectralV K,hbound,
    spectral_reconstruction hd,Or.inr ⟨abs_lt.mp hfree,hend⟩⟩
  simpa only [spectralDet,Complex.mul_im,Complex.star_def,Complex.conj_re,Complex.conj_im,
    neg_mul,sub_eq_add_neg] using hd

end
end IsingBulk.Joint
