import IsingBulk.Joint.Negative.PhysicalObstruction
import IsingBulk.Joint.Negative.TransverseNormalization
import IsingBulk.Anisotropic.RegularEdges.PositiveChartData

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter IsingBulk.Anisotropic IsingBulk.Anisotropic.RegularEdges
open scoped Topology

/-- Actual full-susceptibility obstruction for every nonramified transverse
curve through a negative prime-phase high-temperature boundary point. -/
theorem transverse_negative_high_no_extension {curve : ℂ→Coupling} {z : ℂ} {b : ℝ}
    (hc : AnalyticAt ℂ curve z) (hS : S (curve z)≠0)
    (hB : (transferB (curve z)).im<0)
    (hK : curve z∈frontier highDomain) (hp : p (curve z)^2≠1)
    (he : edgeParameter b (curve z)=0)
    (hd : deriv (fun t=>edgeParameter b (curve t)) z≠0)
    (hprime : b∈primePhaseCosines) :
    ¬HasDomainExtension (curve ⁻¹' highDomain) (FormFactors.highNormalizedBulk∘curve) z := by
  obtain ⟨psi,N,hpa,hp0,hN,hNa,hN0,hchart,_⟩ := normalize_negative_curve hc hS hB he hd
  have hSN : S (N 0)≠0 := by rwa [hN0]
  have hBN : (transferB (N 0)).im<0 := by rwa [hN0]
  have hTN : T (N 0)≠0 := by
    intro h
    exact transferB_ne_zero_of_im_neg hBN (by simp [transferB,h])
  have hPN : p (N 0)≠0 := mul_ne_zero hSN hTN
  have hn := normalized_negative_curve_no_extension hNa (negativeChartRoot_analyticAt hNa hPN)
    hSN hBN (by rwa [hN0]) (by rwa [hN0]) hprime hchart
    (Eventually.of_forall (negativeChartRoot_sq hPN))
  intro hext
  have hmap : MapsTo psi (N ⁻¹' highDomain) (curve ⁻¹' highDomain) := by
    intro t ht
    simpa only [mem_preimage,hN,Function.comp_apply] using ht
  have hcomp := domain_extension_comp_of_mapsTo hpa hp0 hmap hext
  apply hn
  simpa only [hN,Function.comp_assoc] using hcomp

/-- The unscaled edge equation used in the JOINT regular-face statement. -/
theorem transverse_negative_high_no_extension_of_edge_deriv
    {curve : ℂ→Coupling} {z : ℂ} {b : ℝ}
    (hc : AnalyticAt ℂ curve z) (hS : S (curve z)≠0)
    (hB : (transferB (curve z)).im<0)
    (hK : curve z∈frontier highDomain) (hp : p (curve z)^2≠1)
    (he : transferC (curve z)+transferB (curve z)-(b:ℂ)=0)
    (hd : deriv (fun t=>transferC (curve t)+transferB (curve t)-(b:ℂ)) z≠0)
    (hprime : b∈primePhaseCosines) :
    ¬HasDomainExtension (curve ⁻¹' highDomain) (FormFactors.highNormalizedBulk∘curve) z := by
  have hBn := transferB_ne_zero_of_im_neg hB
  have hBa : AnalyticAt ℂ (fun t=>transferB (curve t)) z :=
    (transferB_analyticAt hS).comp hc
  have hEa : AnalyticAt ℂ (fun t=>transferC (curve t)+transferB (curve t)-(b:ℂ)) z :=
    (((transferC_analyticAt hS).comp hc).add hBa).sub analyticAt_const
  have hder := (hEa.differentiableAt.hasDerivAt.div hBa.differentiableAt.hasDerivAt hBn).deriv
  apply transverse_negative_high_no_extension hc hS hB hK hp
    (by simp only [edgeParameter,he,zero_div]) _ hprime
  change deriv ((fun t=>transferC (curve t)+transferB (curve t)-(b:ℂ))/(fun t=>transferB (curve t))) z≠0
  rw [hder,he,zero_mul,sub_zero]
  exact div_ne_zero (mul_ne_zero hd hBn) (pow_ne_zero _ hBn)

end
end IsingBulk.Joint.Negative