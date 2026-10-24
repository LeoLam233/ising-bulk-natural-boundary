import IsingBulk.Anisotropic.NegativeDominance.NegativeShiftedAngles
import IsingBulk.Anisotropic.NegativeDominance.NormalizedAngularMeasure
import IsingBulk.Anisotropic.NegativeDominance.FixedParticleContinuation
import IsingBulk.Anisotropic.RegularEdges.ComplexAngularIdentity

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour IsingBulk.Anisotropic.RegularEdges
open Set MeasureTheory
open scoped BigOperators

def negativeShiftedPeriod (b : ℝ) (B S : ℂ → ℂ) (n : ℕ) (u : ℂ) : ℂ :=
  ((n+1).factorial : ℂ)⁻¹*(-1 : ℂ)^((n+1).choose 2)*
    ∫ v : Fin n → ℝ, negativeShiftedFullIntegrand b B S n u v
      ∂Measure.pi (fun _ => edgeAngleMeasure)

theorem transferW_im_pos_negative_chart {lam b : ℝ} {B : ℂ → ℂ} {z u : ℂ}
    (hB : B u= -spectralT lam z/spectralS z)
    (he : edgeMapV lam (-1) z=(b : ℂ)+u) (hu : 0<u.im) (hBi : 0<(B u).im)
    (q : ℝ) : 0<(transferW lam z (q : ℂ)).im := by
  rw [transferW_eq_negative_edgeParamW hB he]
  have hc : 0≤1-Real.cos (q-Real.pi) := sub_nonneg.mpr (Real.cos_le_one _)
  have hm := mul_nonneg hBi.le hc
  simp only [edgeParamW,Complex.add_im,Complex.ofReal_im,zero_add,Complex.mul_im,
    Complex.sub_re,Complex.one_re,Complex.ofReal_re,Complex.sub_im,Complex.one_im,
    sub_zero,mul_zero]
  linarith

theorem complexAngularDensity_eq_negativeShiftedFullIntegrand (n : ℕ)
    {lam b : ℝ} {B S : ℂ → ℂ} {z u : ℂ}
    (hB : B u= -spectralT lam z/spectralS z) (hS : S u=spectralS z)
    (he : edgeMapV lam (-1) z=(b : ℂ)+u) (hu : 0<u.im) (hBi : 0<(B u).im)
    (v : Fin n → ℝ) :
    complexAngularDensity lam z
      (fun i => (physicalDependentAngles n (fun k => v k+Real.pi) i : ℂ))=
      (-1 : ℂ)^((n+1).choose 2)*negativeShiftedFullIntegrand b B S n u v := by
  let q := physicalDependentAngles n (fun k => v k+Real.pi)
  have hi (i : Fin (n+1)) := transferW_im_pos_negative_chart hB he hu hBi (q i)
  have hz : 1-∏ i,continuedTransferRoot lam z (q i : ℂ)≠0 := by
    apply one_sub_coordinateProduct_ne_zero (by omega : 0<n+1)
    intro i
    simpa only [continuedTransferRoot,continuedRoot_eq_interiorRoot (hi i)] using
      interiorRoot_norm_lt_one (hi i)
  rw [← continuedAngularDensity_eq_complexAngularDensity_of_im_pos lam z _ hi,
    continuedAngularDensity_eq_negative_edgeFullIntegrand hB hS he _ hz]
  unfold negativeShiftedFullIntegrand negativeShiftedAngles
  rw [edgeFullIntegrand_wrapAngle]

theorem continuedAngularCoefficient_eq_negativeShiftedPeriod (n : ℕ)
    {lam b : ℝ} {B S : ℂ → ℂ} {z u : ℂ}
    (hB : B u= -spectralT lam z/spectralS z) (hS : S u=spectralS z)
    (he : edgeMapV lam (-1) z=(b : ℂ)+u) (hu : 0<u.im) (hBi : 0<(B u).im) :
    continuedAngularCoefficient n lam z=negativeShiftedPeriod b B S n u := by
  have hz (q : Fin (n+1) → ℝ) : 1-∏ i,continuedTransferRoot lam z (q i : ℂ)≠0 := by
    apply one_sub_coordinateProduct_ne_zero (by omega : 0<n+1)
    intro i
    have hi := transferW_im_pos_negative_chart hB he hu hBi (q i)
    simpa only [continuedTransferRoot,continuedRoot_eq_interiorRoot hi] using
      interiorRoot_norm_lt_one hi
  unfold continuedAngularCoefficient negativeShiftedPeriod
  rw [angleBox_integral_eq_negative_shifted,edgeAngleMeasure_integral_eq]
  have hd (v : Fin n → ℝ) :
      continuedAngularDensity lam z
        (fun i => (physicalDependentAngles n (fun k => v k+Real.pi) i : ℂ))=
      (-1 : ℂ)^((n+1).choose 2)*negativeShiftedFullIntegrand b B S n u v := by
    rw [continuedAngularDensity_eq_negative_edgeFullIntegrand hB hS he _ (hz _)]
    unfold negativeShiftedFullIntegrand negativeShiftedAngles
    rw [edgeFullIntegrand_wrapAngle]
  simp_rw [hd]
  rw [integral_const_mul]
  ring

theorem unscaledAngularCoefficient_eq_negativeShiftedPeriod (n : ℕ)
    {lam b : ℝ} {B S : ℂ → ℂ} {z u : ℂ}
    (hz : z∉spectralSet lam) (hS0 : spectralS z≠0)
    (hB : B u= -spectralT lam z/spectralS z) (hS : S u=spectralS z)
    (he : edgeMapV lam (-1) z=(b : ℂ)+u) (hu : 0<u.im) (hBi : 0<(B u).im) :
    unscaledAngularCoefficient n lam z=negativeShiftedPeriod b B S n u := by
  rw [← continuedAngularCoefficient_eq_unscaled_of_im_pos n hz hS0
    (transferW_im_pos_negative_chart hB he hu hBi)]
  exact continuedAngularCoefficient_eq_negativeShiftedPeriod n hB hS he hu hBi

/-- Attachment to the literal high-temperature full-site coefficient. -/
theorem unscaledFullCoefficient_eq_negativeShiftedPeriod (n : ℕ)
    {lam b : ℝ} {B S : ℂ → ℂ} {z u : ℂ} (hlam : 0<lam)
    (hz : z∈omegaH lam\{0})
    (hB : B u= -spectralT lam z/spectralS z) (hS : S u=spectralS z)
    (he : edgeMapV lam (-1) z=(b : ℂ)+u) (hu : 0<u.im) (hBi : 0<(B u).im) :
    FormFactors.unscaledFullCoefficient (n+1) lam z=negativeShiftedPeriod b B S n u := by
  rw [unscaledFullCoefficient_eq_angular_omegaH n hlam hz]
  exact unscaledAngularCoefficient_eq_negativeShiftedPeriod n
    (omegaH_subset_spectral_complement hlam hz.1)
    (omegaH_spectralS_ne_zero hlam hz.1 hz.2) hB hS he hu hBi

end
end IsingBulk.Anisotropic.NegativeDominance
