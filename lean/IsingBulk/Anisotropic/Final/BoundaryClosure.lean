import IsingBulk.Anisotropic.Final.BoundaryReduction
import IsingBulk.Anisotropic.Final.IsotropicHighTheorem
import IsingBulk.Anisotropic.Final.IsotropicLowTheorem

namespace IsingBulk.Anisotropic
noncomputable section
open Set FormFactors

theorem high_naturalBoundary_of_oriented
    (hV : ∀ lam, 0<lam → ∀ w∈frontier (omegaH lam), OrientedPrimeVEdge lam w →
      ¬HasDomainExtension (omegaH lam) (highNormalizedBulk lam) w)
    {lam : ℝ} (hlam : 0<lam) {corrH corrL : ℝ → LatticeSite → ℝ}
    (hphys : PublishedRealSpinFormFactors lam corrH corrL) :
    NaturalBoundaryOn (omegaH lam) (highNormalizedBulk lam) := by
  by_cases he : lam=1
  · subst lam
    exact highNormalizedBulk_one_naturalBoundary
  · have hd := frontier_spectral_component_subset_closure_prime_regular hlam he 0
    rw [connectedComponentIn_spectral_complement_zero hlam] at hd
    exact naturalBoundaryOn_of_dense_obstructions (highNormalizedBulk_analyticOnNhd hlam) hd
      (fun _ hz => high_prime_no_extension_of_oriented hV hlam hphys hz.1 hz.2)

theorem low_naturalBoundary_of_oriented
    (hV : ∀ lam, 0<lam → ∀ w∈frontier (omegaL lam), OrientedPrimeVEdge lam w →
      ¬HasDomainExtension (omegaL lam) (lowNormalizedBulk lam) w)
    {lam : ℝ} (hlam : 0<lam) {corrH corrL : ℝ → LatticeSite → ℝ}
    (hphys : PublishedRealSpinFormFactors lam corrH corrL) :
    NaturalBoundaryOn (omegaL lam) (lowNormalizedBulk lam) := by
  by_cases he : lam=1
  · subst lam
    exact lowNormalizedBulk_one_naturalBoundary hphys
  · let x := criticalPoint lam+1
    have hx : criticalPoint lam<x := by dsimp [x]; linarith
    have hd := frontier_spectral_component_subset_closure_prime_regular hlam he (x:ℂ)
    rw [connectedComponentIn_spectral_complement_supercritical hlam hx] at hd
    exact naturalBoundaryOn_of_dense_obstructions (lowNormalizedBulk_analyticOnNhd hlam) hd
      (fun _ hz => low_prime_no_extension_of_oriented hV hlam hphys hz.1 hz.2)

end
end IsingBulk.Anisotropic
