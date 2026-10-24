import IsingBulk.Anisotropic.Final.BoundaryClosure
import IsingBulk.Anisotropic.Final.PhysicalNormalization
import IsingBulk.Anisotropic.RegularEdges.PositiveEndpointHigh
import IsingBulk.Anisotropic.NegativeDominance.NegativeEndpoint

namespace IsingBulk.Anisotropic
noncomputable section
open Set FormFactors RegularEdges NegativeDominance

theorem high_oriented_prime_no_extension {lam : ℝ} (hlam : 0<lam) {z : ℂ}
    (hz : z∈frontier (omegaH lam)) (he : OrientedPrimeVEdge lam z) :
    ¬HasDomainExtension (omegaH lam) (highNormalizedBulk lam) z := by
  obtain ⟨_hd,e,he,hv,hu,hder,hprime,ho⟩ := he
  rcases he with rfl | rfl
  · exact high_positive_prime_no_extension hlam hz (by simpa using ho) hv hu
      (by simpa only [Complex.ofReal_one] using hder) hprime
  · exact high_negative_prime_no_extension hlam hz (by nlinarith) hv hu
      (by simpa only [Complex.ofReal_neg,Complex.ofReal_one] using hder) hprime

/-- Every finite positive coupling ratio, every boundary point, and the
complete infinite odd-particle physical high-temperature bulk. -/
theorem highNormalizedBulk_naturalBoundary {lam : ℝ} (hlam : 0<lam)
    {corrH corrL : ℝ → LatticeSite → ℝ}
    (hphys : PublishedRealSpinFormFactors lam corrH corrL) :
    NaturalBoundaryOn (omegaH lam) (highNormalizedBulk lam) :=
  high_naturalBoundary_of_oriented (fun _ h _ hz he => high_oriented_prime_no_extension h hz he) hlam hphys

theorem highPhysicalBulk_naturalBoundary {J lam : ℝ} (hJ : 0<J) (hlam : 0<lam)
    {corrH corrL : ℝ → LatticeSite → ℝ}
    (hphys : PublishedRealSpinFormFactors lam corrH corrL) :
    NaturalBoundaryOn (omegaH lam) (highPhysicalBulk J lam) := by
  refine ⟨highPhysicalBulk_analyticOnNhd J hlam,?_⟩
  intro z hz
  exact physical_response_no_extension hJ (high_boundary_ne_zero hlam hz)
    ((highNormalizedBulk_naturalBoundary hlam hphys).2 z hz)

end
end IsingBulk.Anisotropic
