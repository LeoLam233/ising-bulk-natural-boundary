import IsingBulk.Joint.Negative.WindingJets
import IsingBulk.Anisotropic.NegativeDominance.PhysicalRestrictedPeriod
import IsingBulk.Joint.Negative.UpperPeriod
import IsingBulk.Joint.Negative.CanonicalJets

namespace IsingBulk.Joint.Negative
noncomputable section
open IsingBulk.Anisotropic IsingBulk.Anisotropic.NegativeDominance
open Set MeasureTheory RegularEdges IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour NegativeCycles
open scoped BigOperators

/-- The exact physically weighted restricted angular integral retains the
Lebesgue/probability normalization and every particle power. -/
theorem weighted_restricted_eq_outerNegativePeriod (n : ℕ)
    {b : ℝ} {B S amp : ℂ→ℂ} {curve : ℂ→Coupling} {u : ℂ}
    (hB : B u= -T (curve u)/IsingBulk.Joint.S (curve u))
    (hS : S u=IsingBulk.Joint.S (curve u))
    (he : transferC (curve u)+transferB (curve u)=(b:ℂ)+u)
    (hu : 0<u.im) (hBi : 0<(B u).im)
    {E : Set (Fin n→ℝ)} (hE : MeasurableSet E)
    (hsub : E⊆Icc (fun _=>-Real.pi) (fun _=>Real.pi)) :
    (∫v in E,weightedShiftedPhysicalDensity n curve amp v u)=
      outerNegativePeriod b B (fun t=>S t/amp t) n E (fun _=>1) u := by
  have hd (v : Fin n→ℝ) :
      continuedAngularDensity (curve u)
        (fun i => (physicalDependentAngles n (fun k=>v k+Real.pi) i:ℂ))=
      (-1:ℂ)^((n+1).choose 2)*negativeShiftedFullIntegrand b B S n u v := by
    have hi (i : Fin (n+1)) := transferW_im_pos_negative_chart hB he hu hBi
      (physicalDependentAngles n (fun k=>v k+Real.pi) i)
    rw [continuedAngularDensity_eq_complexAngularDensity_of_im_pos (curve u) _ hi]
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
end IsingBulk.Joint.Negative
