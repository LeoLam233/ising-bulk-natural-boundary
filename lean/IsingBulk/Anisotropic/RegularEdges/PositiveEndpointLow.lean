import IsingBulk.Anisotropic.RegularEdges.PositiveEndpointHigh
import IsingBulk.Anisotropic.Final.LowPrefactor

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open Set Filter Metric FormFactors
open scoped Topology

/-- Actual positive V-endpoint obstruction for the complete physical LT bulk,
including its normalized physical fourth-root prefactor. -/
theorem low_positive_prime_no_extension {lam : ℝ} (hlam : 0<lam) {z : ℂ}
    (hz : z∈frontier (omegaL lam)) (hd : 0<spectralDet lam z)
    (hv : spectralV lam z=1) (hu : |spectralU lam z|<1)
    (hder : deriv (edgeMapV lam 1) z≠0) (hprime : spectralU lam z∈primePhaseCosines) :
    ¬HasDomainExtension (omegaL lam) (lowNormalizedBulk lam) z := by
  obtain ⟨zeta,hζa,hζ0,r₀,hr₀,hchart⟩ := exists_oriented_V_low_chart hlam hz hd.ne'
    (Or.inl rfl : (1:ℝ)=1 ∨ (1:ℝ)= -1) hv hu hder (by simpa using hd)
  have hdζ : 0<spectralDet lam (zeta 0) := by rw [hζ0]; exact hd
  obtain ⟨r,hr,haζ,hAa,hdata⟩ := exists_positive_chart_data hζa hdζ hr₀ hchart
  have hP0 : spectralProduct lam (zeta 0)≠0 :=
    mul_ne_zero (spectralS_ne_zero_of_det_ne_zero hdζ.ne') (spectralT_ne_zero_of_det_ne_zero hdζ.ne')
  have hPa : AnalyticAt ℂ (fun u => spectralProduct lam (zeta u)) 0 :=
    (spectralProduct_analyticAt_ff lam _).comp hζa
  have hQa : AnalyticAt ℂ (fun u => 1-(spectralProduct lam (zeta u))⁻¹^2) 0 :=
    analyticAt_const.sub ((hPa.inv hP0).pow 2)
  have hQ0 : 1-(spectralProduct lam (zeta 0))⁻¹^2≠0 := by
    intro h
    have hh : ((spectralProduct lam (zeta 0))^2)⁻¹=1 := by
      simpa only [inv_pow] using (sub_eq_zero.mp h).symm
    have hp := inv_eq_one.mp hh
    rw [hζ0] at hp
    exact product_sq_ne_one_of_strictU hd.ne' hu hp
  have hmap : MapsTo zeta (upperBall r) (omegaL lam) :=
    fun u hu => ((hdata u hu.1).2.2.2.2 hu.2).1
  have hfc : ContinuousOn (fun u => lowPrefactor lam (zeta u)) (upperBall r) := by
    intro u hu
    exact (((lowPrefactor_actual_spec hlam).1 _ (hmap hu)).continuousAt.comp
      (haζ u hu.1).continuousAt).continuousWithinAt
  have hfp : ∀u∈upperBall r,(lowPrefactor lam (zeta u))^4=1-(spectralProduct lam (zeta u))⁻¹^2 :=
    fun u hu => (lowPrefactor_actual_spec hlam).2.1 _ (hmap hu)
  have hraw : ∀δ : ℝ,0<δ → δ≤r → ¬HasDomainExtension (upperBall δ) (fun u => ∑'i,
      (spectralProduct lam (zeta u))^(i+1)*unscaledFullCoefficient (2*i+2) lam (zeta u)) 0 := by
    intro δ hδ hδr
    exact (positive_prime_raw_chart_no_extension hlam hu hprime hδ
      (haζ.mono (ball_subset_ball hδr)) (hAa.mono (ball_subset_ball hδr)) hdζ
      (fun _ h => Or.inr h) (fun u hu => hdata u (ball_subset_ball hδr hu))).2
  have hno := no_extension_product_of_upper_fourth_branch hr hQa hQ0 hfc hfp hraw
  intro hext
  apply hno
  simpa only [Function.comp_apply,lowNormalizedBulk] using!
    domain_extension_comp_of_mapsTo hζa hζ0 hmap hext

end
end IsingBulk.Anisotropic.RegularEdges
