import IsingBulk.Anisotropic.Geometry.SpectralSigns

namespace IsingBulk.Anisotropic
noncomputable section

private theorem cone_zero {a b alpha beta f g : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hdet : alpha*beta-a*b ≠ 0)
    (h1 : g*(alpha*f-b*g)=0) (h2 : -f*(a*f-beta*g)=0) : f=0 ∧ g=0 := by
  have hf : f=0 := by
    by_contra hf
    have hv : a*f-beta*g=0 := (mul_eq_zero.mp h2).resolve_left (neg_ne_zero.mpr hf)
    have hg : g≠0 := by
      intro hg
      rw [hg,mul_zero,sub_zero] at hv
      exact (mul_ne_zero ha hf) hv
    have hu := (mul_eq_zero.mp h1).resolve_left hg
    have hp : (alpha*beta-a*b)*f=0 := by linear_combination beta*hu-b*hv
    exact (mul_ne_zero hdet hf) hp
  refine ⟨hf,?_⟩
  rw [hf,mul_zero,zero_sub] at h1
  have : g^2=0 := by
    exact (mul_eq_zero.mp (show b*g^2=0 by nlinarith [h1])).resolve_left hb
  exact sq_eq_zero_iff.mp this

theorem zero_edges_of_collinear (h c H C t q T Q : ℝ)
    (hh : 0<h) (hH : 0<H)
    (hc : c^2-h^2=1) (hC : C^2-H^2=1) (ht : q^2+t^2=1) (hT : Q^2+T^2=1)
    (hq : q ≠ 0 ∨ Q ≠ 0) (hd : h*C*t*Q-c*H*q*T=0)
    (hNu : (c*t*T*Q-h*H*C*q)^2≤(h*C*t*Q-c*H*q*T)^2)
    (hNv : (h*c*H*Q-C*t*q*T)^2≤(h*C*t*Q-c*H*q*T)^2) :
    C^2*t^2-c^2*H^2=0 ∧ c^2*T^2-h^2*C^2=0 := by
  have ha := sq_pos_of_pos hh
  have hb := sq_pos_of_pos hH
  have hdelta : 0 < (H^2+Q^2)*(h^2+q^2)-h^2*H^2 := by
    rcases hq with hq | hQ
    · nlinarith [mul_pos hb (sq_pos_of_ne_zero hq), mul_nonneg (sq_nonneg h) (sq_nonneg Q),
        mul_nonneg (sq_nonneg q) (sq_nonneg Q)]
    · nlinarith [mul_pos ha (sq_pos_of_ne_zero hQ), mul_nonneg (sq_nonneg H) (sq_nonneg q),
        mul_nonneg (sq_nonneg q) (sq_nonneg Q)]
  have hnu : (c*t*T*Q-h*H*C*q)^2=0 := by nlinarith [sq_nonneg (c*t*T*Q-h*H*C*q)]
  have hnv : (h*c*H*Q-C*t*q*T)^2=0 := by nlinarith [sq_nonneg (h*c*H*Q-C*t*q*T)]
  have hu := numeratorU_factor h c H C t q T Q
  have hv := numeratorV_factor h c H C t q T Q
  rw [hnu,hd] at hu
  rw [hnv,hd] at hv
  have he := edge_auxiliary_identities h c H C t q T Q hc hC ht hT
  apply cone_zero ha.ne' hb.ne' hdelta.ne'
  · linear_combination -C^2*hu-(c^2*T^2-h^2*C^2)*he.1
  · linear_combination -c^2*hv+(C^2*t^2-c^2*H^2)*he.2

theorem signs_zero_of_collinear_right {lam : ℝ} (hlam : 0<lam) {z : ℂ}
    (hx : 0<z.re) (hq : Real.sin z.im ≠ 0 ∨ Real.sin (lam*z.im) ≠ 0)
    (hd : spectralDet lam z=0)
    (hf : geometryF1 lam z.re z.im*geometryF2 lam z.re z.im≤0) :
    geometryF1 lam z.re z.im=0 ∧ geometryF2 lam z.re z.im=0 := by
  have hb := (spectral_numerator_bounds_iff_signs hlam hx hq).mpr hf
  rw [spectralNU_formula,spectralNV_formula,spectralDet_formula] at hb
  rw [spectralDet_formula] at hd
  exact zero_edges_of_collinear _ _ _ _ _ _ _ _
    (Real.sinh_pos_iff.mpr hx) (Real.sinh_pos_iff.mpr (mul_pos hlam hx))
    (Real.cosh_sq_sub_sinh_sq _) (Real.cosh_sq_sub_sinh_sq _)
    (Real.sin_sq_add_cos_sq _) (Real.sin_sq_add_cos_sq _) hq hd hb.1 hb.2

/-- The intersection of the two edge equations lies on the unit product locus. -/
theorem edge_intersection_norm_product (h c H C t q T Q : ℝ) (hCpos : 0<C)
    (hc : c^2-h^2=1) (hC : C^2-H^2=1) (ht : q^2+t^2=1) (hT : Q^2+T^2=1)
    (hf : C^2*t^2-c^2*H^2=0) (hg : c^2*T^2-h^2*C^2=0) :
    (h^2+q^2)*(H^2+Q^2)=1 := by
  have hxy : t^2*T^2-h^2*H^2=0 := by
    apply (mul_eq_zero.mp (show C^2*(t^2*T^2-h^2*H^2)=0 by
      linear_combination T^2*hf+H^2*hg)).resolve_left (sq_pos_of_pos hCpos).ne'
  linear_combination (H^2+Q^2)*ht+(h^2-t^2+1)*hT+(-H^2+T^2)*hc+
    (-h^2+t^2)*hC-hf-hg+hxy

end
end IsingBulk.Anisotropic
