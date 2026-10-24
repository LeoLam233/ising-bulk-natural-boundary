import IsingBulk.Anisotropic.Final.BoundaryClosure
import IsingBulk.Anisotropic.Final.PhysicalNormalization
import IsingBulk.Anisotropic.RegularEdges.NegativeLowEndpoint

namespace IsingBulk.Anisotropic
noncomputable section
open Set FormFactors RegularEdges

theorem low_oriented_prime_no_extension {lam : ℝ} (hlam : 0<lam) {z : ℂ}
    (hz : z∈frontier (omegaL lam)) (he : OrientedPrimeVEdge lam z) :
    ¬HasDomainExtension (omegaL lam) (lowNormalizedBulk lam) z := by
  obtain ⟨_hd,e,he,hv,hu,hder,hprime,ho⟩ := he
  rcases he with rfl | rfl
  · exact low_positive_prime_no_extension hlam hz (by simpa using ho) hv hu
      (by simpa only [Complex.ofReal_one] using hder) hprime
  · exact low_negative_prime_no_extension hlam hz (by nlinarith) hv hu
      (by simpa only [Complex.ofReal_neg,Complex.ofReal_one] using hder) hprime

/-- Full pure-phase connected LT natural boundary, every positive finite ratio,
every lattice site, every positive even particle order and every boundary point.
The only premise is the separately typed published real spin representation. -/
theorem lowNormalizedBulk_naturalBoundary {lam : ℝ} (hlam : 0<lam)
    {corrH corrL : ℝ → LatticeSite → ℝ}
    (hphys : PublishedRealSpinFormFactors lam corrH corrL) :
    NaturalBoundaryOn (omegaL lam) (lowNormalizedBulk lam) :=
  low_naturalBoundary_of_oriented (fun _ h _ hz he => low_oriented_prime_no_extension h hz he) hlam hphys

theorem lowPhysicalBulk_naturalBoundary {J lam : ℝ} (hJ : 0<J) (hlam : 0<lam)
    {corrH corrL : ℝ → LatticeSite → ℝ}
    (hphys : PublishedRealSpinFormFactors lam corrH corrL) :
    NaturalBoundaryOn (omegaL lam) (lowPhysicalBulk J lam) := by
  refine ⟨lowPhysicalBulk_analyticOnNhd J hlam,?_⟩
  intro z hz
  exact physical_response_no_extension hJ (low_boundary_ne_zero hlam hz)
    ((lowNormalizedBulk_naturalBoundary hlam hphys).2 z hz)

end
end IsingBulk.Anisotropic
