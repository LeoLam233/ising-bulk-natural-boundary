import IsingBulk.Anisotropic.Geometry.CollinearSigns
import IsingBulk.Anisotropic.Geometry.CollinearRectangle
import IsingBulk.Anisotropic.Geometry.DomainNonvanishing

namespace IsingBulk.Anisotropic
noncomputable section

theorem norm_product_eq_one_of_zero_edges {lam : ℝ} {z : ℂ}
    (hf : geometryF1 lam z.re z.im=0) (hg : geometryF2 lam z.re z.im=0) :
    ‖spectralProduct lam z‖=1 := by
  have hs : ‖spectralS z‖^2=Real.sinh z.re^2+Real.sin z.im^2 := norm_sinh_sq z
  have ht : ‖spectralT lam z‖^2=Real.sinh (lam*z.re)^2+Real.sin (lam*z.im)^2 := by
    simpa only [spectralT,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero,add_zero] using norm_sinh_sq ((lam:ℂ)*z)
  have hp := edge_intersection_norm_product (Real.sinh z.re) (Real.cosh z.re)
    (Real.sinh (lam*z.re)) (Real.cosh (lam*z.re)) (Real.cos z.im) (Real.sin z.im)
    (Real.cos (lam*z.im)) (Real.sin (lam*z.im)) (Real.cosh_pos _)
    (Real.cosh_sq_sub_sinh_sq _) (Real.cosh_sq_sub_sinh_sq _) (Real.sin_sq_add_cos_sq _)
    (Real.sin_sq_add_cos_sq _) hf hg
  rw [← hs,← ht] at hp
  rw [spectralProduct,norm_mul]
  have hn := mul_nonneg (norm_nonneg (spectralS z)) (norm_nonneg (spectralT lam z))
  nlinarith [sq_nonneg (‖spectralS z‖*‖spectralT lam z‖-1)]

theorem mem_spectralSet_of_collinear_zero_edges {lam : ℝ} (hlam : 0<lam) {z : ℂ}
    (hx : 0<z.re) (hd : spectralDet lam z=0)
    (hf : geometryF1 lam z.re z.im=0) (hg : geometryF2 lam z.re z.im=0) : z∈spectralSet lam := by
  have hnV := spectralNV_sq_sub_det_sq lam z
  rw [hd,hf] at hnV
  have hnV0 : spectralNV lam z=0 := by
    apply sq_eq_zero_iff.mp
    simpa using hnV
  have hre : (spectralS z).re ≠ 0 := by
    rw [spectralS_re]
    apply mul_ne_zero (Real.sinh_pos_iff.mpr hx).ne'
    intro hcos
    have hprod := mul_pos (sq_pos_of_pos (Real.cosh_pos z.re))
      (sq_pos_of_pos (Real.sinh_pos_iff.mpr (mul_pos hlam hx)))
    simp only [geometryF1,hcos,zero_pow (by decide : 2≠0),mul_zero,zero_sub] at hf
    linarith
  exact collinear_rectangle_representation _ _ _ hre hd hnV0
    (dispersion_norm_bound _ _ _ (spectralA_sq lam z) (norm_product_eq_one_of_zero_edges hf hg))

theorem zero_edges_of_signs_real_angles {lam : ℝ} {z : ℂ}
    (hq : Real.sin z.im=0) (hQ : Real.sin (lam*z.im)=0)
    (hf : geometryF1 lam z.re z.im*geometryF2 lam z.re z.im≤0) :
    geometryF1 lam z.re z.im=0 ∧ geometryF2 lam z.re z.im=0 := by
  have ht : Real.cos z.im^2=1 := by simpa [hq] using Real.sin_sq_add_cos_sq z.im
  have hT : Real.cos (lam*z.im)^2=1 := by simpa [hQ] using Real.sin_sq_add_cos_sq (lam*z.im)
  have he : geometryF1 lam z.re z.im=geometryF2 lam z.re z.im := by
    unfold geometryF1 geometryF2
    rw [ht,hT]
    linear_combination -Real.cosh (lam*z.re)^2*Real.cosh_sq_sub_sinh_sq z.re+
      Real.cosh z.re^2*Real.cosh_sq_sub_sinh_sq (lam*z.re)
  have hz : geometryF1 lam z.re z.im=0 := by
    rw [← he] at hf
    nlinarith [sq_nonneg (geometryF1 lam z.re z.im)]
  exact ⟨hz,he ▸ hz⟩

/-- Full right-half-plane equivalence, with collinear points resolved by an unsquared segment proof. -/
theorem mem_spectralSet_iff_signs_right {lam : ℝ} (hlam : 0<lam) {z : ℂ} (hx : 0<z.re) :
    z∈spectralSet lam ↔ geometryF1 lam z.re z.im*geometryF2 lam z.re z.im≤0 := by
  constructor
  · exact geometry_signs_of_mem_right hlam hx
  · intro hf
    by_cases hd : spectralDet lam z ≠ 0
    · exact (mem_spectralSet_iff_signs_of_det_ne_zero hlam hx hd).mpr hf
    · push Not at hd
      by_cases hq : Real.sin z.im ≠ 0 ∨ Real.sin (lam*z.im) ≠ 0
      · have he := signs_zero_of_collinear_right hlam hx hq hd hf
        exact mem_spectralSet_of_collinear_zero_edges hlam hx hd he.1 he.2
      · push Not at hq
        have he := zero_edges_of_signs_real_angles hq.1 hq.2 hf
        exact mem_spectralSet_of_collinear_zero_edges hlam hx hd he.1 he.2

/-- The exact spectral set (2.3), for every positive anisotropy, without discarded degeneracies. -/
theorem mem_spectralSet_iff_signs {lam : ℝ} (hlam : 0<lam) (z : ℂ) :
    z∈spectralSet lam ↔ geometryF1 lam z.re z.im*geometryF2 lam z.re z.im≤0 := by
  constructor
  · exact geometry_signs_of_mem hlam
  · intro hf
    rcases lt_trichotomy z.re 0 with hx | hx | hx
    · apply (neg_mem_spectralSet_iff lam z).mp
      apply (mem_spectralSet_iff_signs_right hlam (z := -z) (by simpa using neg_pos.mpr hx)).mpr
      simpa [geometryF1,geometryF2,Complex.neg_re,Complex.neg_im,mul_neg,
        Real.cosh_neg,Real.sinh_neg,Real.cos_neg] using hf
    · have he : z=(z.im:ℂ)*Complex.I := by apply Complex.ext <;> simp [hx]
      rw [he]
      exact (imaginary_geometry_iff lam z.im).mp (by simpa [hx] using hf)
    · exact (mem_spectralSet_iff_signs_right hlam hx).mpr hf

end
end IsingBulk.Anisotropic
