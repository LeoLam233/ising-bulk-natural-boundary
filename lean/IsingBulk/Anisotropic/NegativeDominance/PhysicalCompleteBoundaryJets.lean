import IsingBulk.Anisotropic.NegativeDominance.CompleteScaledUpperBoundaryJets
import IsingBulk.Anisotropic.FormFactors.WeightedParticleSeriesJets

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.Anisotropic.RegularEdges Set Filter
open scoped Topology

/-- Actual full weighted HT particle series, up to the common analytic
square-root factor. Every derivative and the complete boundary sum are attached. -/
theorem physical_scaled_high_series_boundary_jets
    {ι : Type*} {l : Filter ι} [NeBot l] {path : ι → ℂ}
    {lam b : ℝ} {B S A zeta : ℂ → ℂ} {U : Set ℂ}
    (hlam : 0<lam) (hb : |b|<1) (hB0 : 0<(B 0).im) (hBa : AnalyticAt ℂ B 0)
    (hSa : AnalyticAt ℂ S 0) (hSzero : S 0≠0)
    (hAa0 : AnalyticAt ℂ A 0) (hA0 : A 0≠0)
    (hzeta : AnalyticAt ℂ zeta 0)
    (hSedge : spectralS (zeta 0)≠0)
    (hedge : spectralA lam (zeta 0)+spectralT lam (zeta 0)=(b : ℂ)*spectralS (zeta 0))
    (hBedge : 0<(-spectralT lam (zeta 0)/spectralS (zeta 0)).im)
    (hU : IsOpen U) (ha : AnalyticOnNhd ℂ zeta U) (hAa : AnalyticOnNhd ℂ A U)
    (hzH : ∀ u∈U, zeta u∈omegaH lam\{0})
    (hS0 : ∀ u∈U, spectralS (zeta u)≠0)
    (hB : ∀ u∈U, B u= -spectralT lam (zeta u)/spectralS (zeta u))
    (hS : ∀ u∈U, S u=spectralS (zeta u))
    (he : ∀ u∈U, edgeMapV lam (-1) (zeta u)=(b : ℂ)+u)
    (hup : ∀ u∈U, 0<u.im) (hBi : ∀ u∈U, 0<(B u).im)
    (hAsq : ∀ u∈U, (A u)^2=spectralProduct lam (zeta u))
    (hAne : ∀ u∈U, A u≠0)
    (hp : Tendsto path l (𝓝 0)) (hin : ∀ᶠ t in l, path t∈U) (j : ℕ) :
    Tendsto (fun t : ι => iteratedDeriv j (fun v => A v*
      ∑' n : ℕ, (spectralProduct lam (zeta v))^n*
        FormFactors.unscaledFullCoefficient (2*n+1) lam (zeta v)) (path t))
      l
      (𝓝 (∑' n : ℕ, iteratedDeriv j
        (fun u => (A u)^(2*n+1)*continuedAngularCoefficient (2*n) lam (zeta u)) 0)) := by
  have hz (u : ℂ) (hu : u∈U) : zeta u∉spectralSet lam :=
    omegaH_subset_spectral_complement hlam (hzH u hu).1
  have hlim := complete_odd_scaledNegativePeriod_boundary_jets_upper
    hb hB0 hBa hSa hSzero hAa0 hA0 hzeta hSedge hedge hBedge hU ha hAa hz hS0
      hB hS he hup hBi hp hin j
  apply hlim.congr'
  filter_upwards [hin] with t ht
  have hj := FormFactors.high_particleSeries_mul_comp_hasSum_iteratedDeriv lam
    (hAa _ ht) (ha _ ht) (hz _ ht) j
  have heq (n : ℕ) :
      (fun v => A v*((spectralProduct lam (zeta v))^n*
        FormFactors.unscaledFullCoefficient (2*n+1) lam (zeta v))) =ᶠ[𝓝 (path t)]
      negativeShiftedPeriod b B (fun v => S v/A v) (2*n) := by
    filter_upwards [hU.mem_nhds ht] with v hv
    rw [weighted_fullCoefficient_eq_scaledPeriod n hlam (hzH v hv) (hB v hv)
      (hS v hv) (he v hv) (hup v hv) (hBi v hv) (hAsq v hv) (hAne v hv)]
    rw [← mul_assoc,mul_inv_cancel₀ (hAne v hv),one_mul]
  rw [← hj.tsum_eq]
  apply tsum_congr
  intro n
  exact ((heq n).iteratedDeriv_eq j).symm

end
end IsingBulk.Anisotropic.NegativeDominance
