import IsingBulk.Anisotropic.NegativeDominance.ContinuationDensity

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour IsingBulk.Anisotropic.RegularEdges
open Set Filter MeasureTheory
open scoped BigOperators Topology

/-- Every fixed odd-particle literal angular integral has an analytic germ
through a regular negative edge. All one-body, pair and lattice denominators
are checked on the full constrained angular torus. -/
theorem continuedAngularCoefficient_negative_analyticAt (n : ℕ) (hN : Odd (n+1))
    {lam b : ℝ} {z : ℂ} (hS : spectralS z≠0)
    (hedge : spectralA lam z+spectralT lam z=(b : ℂ)*spectralS z)
    (hb : |b|<1) (hB : 0<(-spectralT lam z/spectralS z).im) :
    AnalyticAt ℂ (continuedAngularCoefficient n lam) z := by
  let psi : (Fin n → ℝ) → (Fin (n+1) → ℂ) :=
    fun q i => (physicalDependentAngles n q i : ℂ)
  have hpsi : Continuous psi := continuous_pi (fun i => Complex.continuous_ofReal.comp
    ((continuous_apply i).comp (physicalDependentAngles_continuous n)))
  let F : ℂ × (Fin (n+1) → ℂ) → ℂ := fun p => continuedAngularDensity lam p.1 p.2
  have hF0 (q : Fin n → ℝ) : AnalyticAt ℂ F (z,psi q) :=
    continuedAngularDensity_negative_joint_analyticAt hN hS hedge hb hB
      (physicalDependentAngles n q) (physicalDependentAngles_sum_zero n q)
  have he : ∀ᶠ w in 𝓝 z, ∀ q∈angleBox n, AnalyticAt ℂ F (w,psi q) := by
    apply (isCompact_Icc : IsCompact (angleBox n)).eventually_forall_of_forall_eventually
    intro q _
    have hc : Continuous (fun p : ℂ × (Fin n → ℝ) => (p.1,psi p.2)) :=
      continuous_fst.prodMk (hpsi.comp continuous_snd)
    exact hc.continuousAt.eventually (hF0 q).eventually_analyticAt
  obtain ⟨U, hU, hUopen, hzU⟩ := mem_nhds_iff.mp he
  have ha := compact_analytic_shape_integral_analyticAt
    (μ := volume) (K := angleBox n) isCompact_Icc hUopen F psi hpsi
    (fun _ => (1 : ℂ)) continuous_const (fun w hw q hq => hU hw q hq) hzU
  have hi : AnalyticAt ℂ (fun w => ∫ q in angleBox n, F (w,psi q)) z := by
    simpa only [one_mul] using ha
  exact analyticAt_const.mul hi

/-- On the actual physical upper root sheet the continuation germ equals the
literal angular coefficient, with all original normalization factors. -/
theorem continuedAngularCoefficient_eq_unscaled_of_im_pos (n : ℕ)
    {lam : ℝ} {z : ℂ} (hz : z∉spectralSet lam) (hS : spectralS z≠0)
    (hi : ∀ q : ℝ, 0<(transferW lam z (q : ℂ)).im) :
    continuedAngularCoefficient n lam z=unscaledAngularCoefficient n lam z := by
  have hcont : Continuous (fun q : Fin n → ℝ => complexAngularDensity lam z
      (fun i => (physicalDependentAngles n q i : ℂ))) := by
    apply continuous_iff_continuousAt.mpr
    intro q
    have hpsi : Continuous (fun q : Fin n → ℝ =>
        (z,fun i => (physicalDependentAngles n q i : ℂ))) :=
      continuous_const.prodMk (continuous_pi (fun i => Complex.continuous_ofReal.comp
        ((continuous_apply i).comp (physicalDependentAngles_continuous n))))
    exact (complexAngularDensity_joint_analyticAt (by omega) hz hS
      (physicalDependentAngles n q)).continuousAt.comp
      (f := fun q : Fin n → ℝ => (z,fun i => (physicalDependentAngles n q i : ℂ)))
      hpsi.continuousAt
  have he : (fun q : Fin n → ℝ => continuedAngularDensity lam z
      (fun i => (physicalDependentAngles n q i : ℂ)))=
      (fun q : Fin n → ℝ => complexAngularDensity lam z
      (fun i => (physicalDependentAngles n q i : ℂ))) := by
    funext q
    exact continuedAngularDensity_eq_complexAngularDensity_of_im_pos lam z _ (fun i => hi _)
  unfold continuedAngularCoefficient unscaledAngularCoefficient
  rw [he, multiAngleIntegral_eq_box n _ hcont]

end
end IsingBulk.Anisotropic.NegativeDominance
