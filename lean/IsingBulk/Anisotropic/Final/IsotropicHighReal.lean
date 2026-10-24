import IsingBulk.Anisotropic.Final.IsotropicCoefficients
import IsingBulk.HT.Final.PublishedPhysicalIdentification

namespace IsingBulk.Anisotropic
noncomputable section
open FormFactors IsingBulk.HT.Contour IsingBulk.HT.Final

theorem isotropic_high_real_parameters {x : ℝ} (hx : 0<x) (hxc : x<criticalPoint 1) :
    0<Real.sinh x ∧ Real.sinh x<1 ∧ realProduct 1 x≠1 := by
  have hs := Real.sinh_pos_iff.mpr hx
  have hp := highRealRadicand_pos (by norm_num : (0:ℝ)<1) hx.le hxc
  rw [realProduct_one] at hp
  have hs1 : Real.sinh x<1 := by
    by_contra hn
    have hss : 1≤Real.sinh x^2 := by nlinarith
    nlinarith [sq_nonneg (Real.sinh x^2-1)]
  refine ⟨hs,hs1,?_⟩
  rw [realProduct_one]
  nlinarith

theorem isotropic_high_weighted_term (n : ℕ) {x : ℝ}
    (hx : 0<x) (hxc : x<criticalPoint 1) :
    spectralProduct 1 (x:ℂ)^n*unscaledFullCoefficient (2*n+1) 1 (x:ℂ) =
      (Real.sinh x:ℂ)⁻¹*physicalAngularCoefficient (2*n) (Real.sinh x)⁻¹ := by
  obtain ⟨hs,hs1,hp⟩ := isotropic_high_real_parameters hx hxc
  have hsi : 1<(Real.sinh x)⁻¹ := (one_lt_inv₀ hs).mpr hs1
  have he := isotropic_scaled_coefficient_eq_angular (2*n) hx hsi
    (by rw [inv_inv,add_comm]) hp
  have hsn : (Real.sinh x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hs.ne'
  rw [← he]
  simp only [spectralProduct,spectralS,spectralT,Complex.ofReal_one,one_mul,← Complex.ofReal_sinh]
  field_simp
  ring

theorem isotropic_high_real_eq {x : ℝ} (hx : 0<x) (hxc : x<criticalPoint 1) :
    highNormalizedBulk 1 (x:ℂ) = interiorFullBulk (Real.sinh x:ℂ) := by
  obtain ⟨hs,hs1,_hp⟩ := isotropic_high_real_parameters hx hxc
  rw [interiorFullBulk_publishedAngularRepresentation (Real.sinh x) hs hs1]
  unfold highNormalizedBulk
  simp_rw [isotropic_high_weighted_term _ hx hxc]
  rw [tsum_mul_left,highPrefactor_real (by norm_num : (0:ℝ)<1) hx.le hxc]
  have ht : 0≤1-realProduct 1 x^2 := (highRealRadicand_pos (by norm_num) hx.le hxc).le
  have he : Complex.ofReal (Real.rpow (1-realProduct 1 x^2) (1/4)) =
      (Complex.ofReal (1-realProduct 1 x^2))^(Complex.ofReal (1/4)) :=
    Complex.ofReal_cpow ht (1/4)
  rw [he]
  simp only [realProduct_one,Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_pow,
    Complex.ofReal_div,Complex.ofReal_ofNat]
  unfold interiorPrefactor publishedAngularOddSeries
  ring_nf

end
end IsingBulk.Anisotropic
