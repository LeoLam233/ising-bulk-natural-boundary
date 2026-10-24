import IsingBulk.Anisotropic.NegativeDominance.BoundaryJetObstruction
import IsingBulk.Anisotropic.RegularEdges.LeadingPrimeCharts
import IsingBulk.Anisotropic.RegularEdges.PositiveChartData
import IsingBulk.Anisotropic.Final.HighPrefactor
import IsingBulk.Anisotropic.Final.AnalyticFactor

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Set Filter FormFactors RegularEdges
open scoped Topology

/-- Transfer actual zero-radius scaled HT boundary jets through the physical
fourth-root prefactor and an actual analytic chart. The branch agreement is on
an open overlap; a ray-only equality is not substituted for that agreement. -/
theorem high_no_extension_of_chart_jets_zero_radius
    {lam : ℝ} {z : ℂ} {D : Set ℂ} {zeta A b : ℂ → ℂ}
    (hD : IsOpen D) (hzeta : AnalyticAt ℂ zeta 0) (hz0 : zeta 0=z)
    (hmap : MapsTo zeta D (omegaH lam))
    (hA : AnalyticAt ℂ A 0) (hb : AnalyticAt ℂ b 0) (hb0 : b 0≠0)
    (hbranch : EqOn b (fun t => highPrefactor lam (zeta t)) D)
    {ι : Type*} {l : Filter ι} [NeBot l] {path : ι → ℂ}
    (hpath : Tendsto path l (𝓝 0)) (hinside : ∀ᶠ t in l, path t∈D)
    (a : ℕ → ℂ)
    (hjets : ∀ j, Tendsto (fun t => iteratedDeriv j
      (fun u => A u*∑' n : ℕ, (spectralProduct lam (zeta u))^n*
        unscaledFullCoefficient (2*n+1) lam (zeta u)) (path t)/(j.factorial:ℂ)) l (𝓝 (a j)))
    (hradius : (FormalMultilinearSeries.ofScalars ℂ a).radius=0) :
    ¬HasDomainExtension (omegaH lam) (highNormalizedBulk lam) z := by
  intro he
  have hp := domain_extension_comp_of_mapsTo hzeta hz0 hmap he
  let raw : ℂ → ℂ := fun u => ∑' n : ℕ, (spectralProduct lam (zeta u))^n*
    unscaledFullCoefficient (2*n+1) lam (zeta u)
  have heq : EqOn (b*raw) (highNormalizedBulk lam ∘ zeta) D := by
    intro t ht
    change b t*raw t=highPrefactor lam (zeta t)*raw t
    rw [hbranch ht]
  have hraw := domain_extension_of_analytic_factor hb hb0 (domain_extension_of_eqOn heq hp)
  have hs := domain_extension_mul_analyticAt hA hraw
  exact no_domain_extension_of_boundary_jets_zero_radius a hD hpath hinside hjets hradius hs

end
end IsingBulk.Anisotropic.NegativeDominance
