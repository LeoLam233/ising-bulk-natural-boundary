import IsingBulk.Anisotropic.NegativeDominance.FixedParticleContinuation

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Anisotropic.RegularEdges

/-- Exact negative-endpoint decomposition of the actual transfer dispersion. -/
theorem transferW_negative_endpoint_decomposition {lam : ℝ} {z : ℂ}
    (hS : spectralS z≠0) (q : ℝ) :
    transferW lam z (q : ℂ)=(spectralA lam z+spectralT lam z)/spectralS z+
      (-spectralT lam z/spectralS z)*(1+(Real.cos q : ℂ)) := by
  unfold transferW
  rw [← Complex.ofReal_cos]
  field_simp [hS]
  ring

theorem transferW_im_pos_of_negative_endpoint {lam : ℝ} {z : ℂ}
    (hS : spectralS z≠0)
    (he : 0<((spectralA lam z+spectralT lam z)/spectralS z).im)
    (hB : 0≤(-spectralT lam z/spectralS z).im) (q : ℝ) :
    0<(transferW lam z (q : ℂ)).im := by
  rw [transferW_negative_endpoint_decomposition hS]
  simp only [Complex.add_im, Complex.mul_im, Complex.add_re, Complex.one_re,
    Complex.ofReal_re, Complex.one_im, Complex.ofReal_im, add_zero, mul_zero, zero_add]
  have hc : 0≤1+Real.cos q := by linarith [Real.neg_one_le_cos q]
  nlinarith only [he, mul_nonneg hB hc]

theorem continuedAngularCoefficient_eq_unscaled_on_negative_sheet (n : ℕ)
    {lam : ℝ} {z : ℂ} (hz : z∉spectralSet lam) (hS : spectralS z≠0)
    (he : 0<((spectralA lam z+spectralT lam z)/spectralS z).im)
    (hB : 0≤(-spectralT lam z/spectralS z).im) :
    continuedAngularCoefficient n lam z=unscaledAngularCoefficient n lam z :=
  continuedAngularCoefficient_eq_unscaled_of_im_pos n hz hS
    (transferW_im_pos_of_negative_endpoint hS he hB)

end
end IsingBulk.Anisotropic.NegativeDominance
