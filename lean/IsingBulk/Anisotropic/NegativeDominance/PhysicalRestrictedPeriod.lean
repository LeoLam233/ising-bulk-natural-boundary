import IsingBulk.Anisotropic.NegativeDominance.OuterBoundaryJetsCauchy
import IsingBulk.Anisotropic.NegativeDominance.ParticleWeightScaling
import IsingBulk.Anisotropic.NegativeCycles.PhysicalWindingJets

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Set MeasureTheory RegularEdges IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour NegativeCycles
open scoped BigOperators

theorem edgeAngleMeasure_restricted_integral_eq (n : ℕ) {E : Set (Fin n→ℝ)}
    (hE : MeasurableSet E) (hsub : E⊆Icc (fun _=>-Real.pi) (fun _=>Real.pi))
    (g : (Fin n→ℝ)→ℂ) :
    (∫v in E,g v ∂Measure.pi (fun _=>edgeAngleMeasure))=
      ((2*Real.pi:ℂ)⁻¹)^n*∫v in E,g v := by
  rw [edgeAngleMeasure_pi_eq,Measure.restrict_smul,integral_smul_measure,
    Measure.restrict_restrict hE,inter_eq_left.mpr hsub]
  simp only [ENNReal.toReal_pow,ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (by positivity : 0≤2*Real.pi),Complex.real_smul,
    Complex.ofReal_pow,Complex.ofReal_inv,Complex.ofReal_mul,Complex.ofReal_ofNat]

/-- The exact physically weighted restricted angular integral retains the
Lebesgue/probability normalization and every particle power. -/
theorem weighted_restricted_eq_outerNegativePeriod (n : ℕ)
    {lam b : ℝ} {B S A zeta : ℂ→ℂ} {u : ℂ}
    (hB : B u= -spectralT lam (zeta u)/spectralS (zeta u))
    (hS : S u=spectralS (zeta u))
    (he : edgeMapV lam (-1) (zeta u)=(b:ℂ)+u)
    (hu : 0<u.im) (hBi : 0<(B u).im)
    {E : Set (Fin n→ℝ)} (hE : MeasurableSet E)
    (hsub : E⊆Icc (fun _=>-Real.pi) (fun _=>Real.pi)) :
    (∫v in E,weightedShiftedPhysicalDensity n lam zeta A v u)=
      outerNegativePeriod b B (fun t=>S t/A t) n E (fun _=>1) u := by
  have hd (v : Fin n→ℝ) :
      continuedAngularDensity lam (zeta u)
        (fun i => (physicalDependentAngles n (fun k=>v k+Real.pi) i:ℂ))=
      (-1:ℂ)^((n+1).choose 2)*negativeShiftedFullIntegrand b B S n u v := by
    have hi (i : Fin (n+1)) := transferW_im_pos_negative_chart hB he hu hBi
      (physicalDependentAngles n (fun k=>v k+Real.pi) i)
    rw [continuedAngularDensity_eq_complexAngularDensity_of_im_pos lam (zeta u) _ hi]
    exact complexAngularDensity_eq_negativeShiftedFullIntegrand n hB hS he hu hBi v
  unfold weightedShiftedPhysicalDensity outerNegativePeriod
  simp_rw [hd,negativeShiftedFullIntegrand_div_scale,one_mul]
  rw [edgeAngleMeasure_restricted_integral_eq n hE hsub,
    integral_const_mul,integral_const_mul,integral_const_mul]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring_nf
  norm_num
  ring

end
end IsingBulk.Anisotropic.NegativeDominance
