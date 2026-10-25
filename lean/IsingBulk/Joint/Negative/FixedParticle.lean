import IsingBulk.Joint.Negative.AngularDensity
import IsingBulk.Joint.Negative.RestrictedJets

namespace IsingBulk.Joint.Negative
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour IsingBulk.Anisotropic.RegularEdges
open Set Filter MeasureTheory
open scoped BigOperators Topology

/-- On the actual physical upper root sheet the continuation germ equals the
literal angular coefficient, with all original normalization factors. -/
theorem continuedAngularCoefficient_eq_unscaled_of_im_pos (n : ℕ)
    {K : Coupling} (hz : K∉spectralSet) (hS : S K≠0)
    (hi : ∀ q : ℝ, 0<(transferW K (q : ℂ)).im) :
    continuedAngularCoefficient n K=unscaledAngularCoefficient n K := by
  have hcont : Continuous (fun q : Fin n → ℝ => complexAngularDensity K
      (fun i => (physicalDependentAngles n q i : ℂ))) := by
    apply continuous_iff_continuousAt.mpr
    intro q
    have hpsi : Continuous (fun q : Fin n → ℝ =>
        (K,fun i => (physicalDependentAngles n q i : ℂ))) :=
      continuous_const.prodMk (continuous_pi (fun i => Complex.continuous_ofReal.comp
        ((continuous_apply i).comp (physicalDependentAngles_continuous n))))
    exact (complexAngularDensity_joint_analyticAt (by omega) hz hS
      (physicalDependentAngles n q)).continuousAt.comp
      (f := fun q : Fin n → ℝ => (K,fun i => (physicalDependentAngles n q i : ℂ)))
      hpsi.continuousAt
  have he : (fun q : Fin n → ℝ => continuedAngularDensity K
      (fun i => (physicalDependentAngles n q i : ℂ)))=
      (fun q : Fin n → ℝ => complexAngularDensity K
      (fun i => (physicalDependentAngles n q i : ℂ))) := by
    funext q
    exact continuedAngularDensity_eq_complexAngularDensity_of_im_pos K _ (fun i => hi _)
  unfold continuedAngularCoefficient unscaledAngularCoefficient
  rw [he, multiAngleIntegral_eq_box n _ hcont]

/-- Every actual weighted odd coefficient is analytic along every analytic
independent-coupling curve through a negative regular edge. -/
theorem weighted_coefficient_negative_analyticAt (n : ℕ) (hn : Odd (n+1))
    {b : ℝ} {curve : ℂ→Coupling} {amp : ℂ→ℂ}
    (hc : AnalyticAt ℂ curve 0) (ha : AnalyticAt ℂ amp 0)
    (hS : S (curve 0)≠0) (hedge : A (curve 0)+T (curve 0)=(b:ℂ)*S (curve 0))
    (hb : |b|<1) (hB : 0<(-T (curve 0)/S (curve 0)).im) :
    AnalyticAt ℂ (fun t=>amp t^(n+1)*continuedAngularCoefficient n (curve t)) 0 := by
  obtain ⟨r,hr,hjets⟩ := paper_restricted_boundary_jets n hn hc ha hS hedge hb hB
  have h := (hjets (Icc (fun _=>-Real.pi) (fun _=>Real.pi)) (fun _ h=>h)).1 0
    (Metric.mem_ball_self hr)
  simpa only [paperShiftedDensity_integral] using h

end
end IsingBulk.Joint.Negative
