import IsingBulk.Joint.Negative.UpperDensity
import IsingBulk.Joint.Negative.FixedParticle
import IsingBulk.Anisotropic.NegativeDominance.NegativeShiftedPeriod

namespace IsingBulk.Joint.Negative
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour IsingBulk.Anisotropic.RegularEdges
open IsingBulk.Anisotropic.NegativeDominance Set MeasureTheory
open scoped BigOperators

theorem transferW_im_pos_negative_chart {b : ℝ} {B : ℂ → ℂ} {K : Coupling} {u : ℂ}
    (hB : B u= -T K/IsingBulk.Joint.S K)
    (he : transferC K+transferB K=(b : ℂ)+u) (hu : 0<u.im) (hBi : 0<(B u).im)
    (q : ℝ) : 0<(transferW K (q : ℂ)).im := by
  rw [transferW_eq_negative_edgeParamW hB he]
  have hc : 0≤1-Real.cos (q-Real.pi) := sub_nonneg.mpr (Real.cos_le_one _)
  have hm := mul_nonneg hBi.le hc
  simp only [edgeParamW,Complex.add_im,Complex.ofReal_im,zero_add,Complex.mul_im,
    Complex.sub_re,Complex.one_re,Complex.ofReal_re,Complex.sub_im,Complex.one_im,
    sub_zero,mul_zero]
  linarith

theorem complexAngularDensity_eq_negativeShiftedFullIntegrand (n : ℕ)
    {b : ℝ} {B S : ℂ → ℂ} {K : Coupling} {u : ℂ}
    (hB : B u= -T K/IsingBulk.Joint.S K) (hS : S u=IsingBulk.Joint.S K)
    (he : transferC K+transferB K=(b : ℂ)+u) (hu : 0<u.im) (hBi : 0<(B u).im)
    (v : Fin n → ℝ) :
    complexAngularDensity K
      (fun i => (physicalDependentAngles n (fun k => v k+Real.pi) i : ℂ))=
      (-1 : ℂ)^((n+1).choose 2)*negativeShiftedFullIntegrand b B S n u v := by
  let q := physicalDependentAngles n (fun k => v k+Real.pi)
  have hi (i : Fin (n+1)) := transferW_im_pos_negative_chart hB he hu hBi (q i)
  have hz : 1-∏ i,continuedTransferRoot K (q i : ℂ)≠0 := by
    apply one_sub_coordinateProduct_ne_zero (by omega : 0<n+1)
    intro i
    simpa only [continuedTransferRoot,continuedRoot_eq_interiorRoot (hi i)] using
      interiorRoot_norm_lt_one (hi i)
  rw [← continuedAngularDensity_eq_complexAngularDensity_of_im_pos K _ hi,
    continuedAngularDensity_eq_negative_edgeFullIntegrand hB hS he _ hz]
  unfold negativeShiftedFullIntegrand negativeShiftedAngles
  rw [edgeFullIntegrand_wrapAngle]

theorem continuedAngularCoefficient_eq_negativeShiftedPeriod (n : ℕ)
    {b : ℝ} {B S : ℂ → ℂ} {K : Coupling} {u : ℂ}
    (hB : B u= -T K/IsingBulk.Joint.S K) (hS : S u=IsingBulk.Joint.S K)
    (he : transferC K+transferB K=(b : ℂ)+u) (hu : 0<u.im) (hBi : 0<(B u).im) :
    continuedAngularCoefficient n K=negativeShiftedPeriod b B S n u := by
  have hz (q : Fin (n+1) → ℝ) : 1-∏ i,continuedTransferRoot K (q i : ℂ)≠0 := by
    apply one_sub_coordinateProduct_ne_zero (by omega : 0<n+1)
    intro i
    have hi := transferW_im_pos_negative_chart hB he hu hBi (q i)
    simpa only [continuedTransferRoot,continuedRoot_eq_interiorRoot hi] using
      interiorRoot_norm_lt_one hi
  unfold continuedAngularCoefficient negativeShiftedPeriod
  rw [angleBox_integral_eq_negative_shifted,edgeAngleMeasure_integral_eq]
  have hd (v : Fin n → ℝ) :
      continuedAngularDensity K
        (fun i => (physicalDependentAngles n (fun k => v k+Real.pi) i : ℂ))=
      (-1 : ℂ)^((n+1).choose 2)*negativeShiftedFullIntegrand b B S n u v := by
    rw [continuedAngularDensity_eq_negative_edgeFullIntegrand hB hS he _ (hz _)]
    unfold negativeShiftedFullIntegrand negativeShiftedAngles
    rw [edgeFullIntegrand_wrapAngle]
  simp_rw [hd]
  rw [integral_const_mul]
  ring

theorem unscaledAngularCoefficient_eq_negativeShiftedPeriod (n : ℕ)
    {b : ℝ} {B S : ℂ → ℂ} {K : Coupling} {u : ℂ}
    (hz : K∉spectralSet) (hS0 : IsingBulk.Joint.S K≠0)
    (hB : B u= -T K/IsingBulk.Joint.S K) (hS : S u=IsingBulk.Joint.S K)
    (he : transferC K+transferB K=(b : ℂ)+u) (hu : 0<u.im) (hBi : 0<(B u).im) :
    unscaledAngularCoefficient n K=negativeShiftedPeriod b B S n u := by
  rw [← continuedAngularCoefficient_eq_unscaled_of_im_pos n hz hS0
    (transferW_im_pos_negative_chart hB he hu hBi)]
  exact continuedAngularCoefficient_eq_negativeShiftedPeriod n hB hS he hu hBi


end
end IsingBulk.Joint.Negative
