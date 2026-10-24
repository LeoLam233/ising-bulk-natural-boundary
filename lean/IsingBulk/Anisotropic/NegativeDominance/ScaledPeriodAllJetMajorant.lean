import IsingBulk.Anisotropic.NegativeDominance.CompleteScaledUpperBoundaryJets

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.Anisotropic.RegularEdges Set Filter
open scoped Topology

/-- Genuine all-particle summable envelopes, with the finite initial indices
included by their proved continuation limits. -/
theorem scaledNegativePeriod_all_jet_majorant_upper
    {ι : Type*} {l : Filter ι} [NeBot l] {path : ι → ℂ}
    {lam b : ℝ} {B S A zeta : ℂ → ℂ} {U : Set ℂ}
    (hb : |b|<1) (hB0 : 0<(B 0).im) (hBa : AnalyticAt ℂ B 0)
    (hSa : AnalyticAt ℂ S 0) (hSzero : S 0≠0)
    (hAa0 : AnalyticAt ℂ A 0) (hA0 : A 0≠0)
    (hzeta : AnalyticAt ℂ zeta 0)
    (hSedge : spectralS (zeta 0)≠0)
    (hedge : spectralA lam (zeta 0)+spectralT lam (zeta 0)=(b : ℂ)*spectralS (zeta 0))
    (hBedge : 0<(-spectralT lam (zeta 0)/spectralS (zeta 0)).im)
    (hU : IsOpen U) (ha : AnalyticOnNhd ℂ zeta U) (hAa : AnalyticOnNhd ℂ A U)
    (hz : ∀ u∈U, zeta u∉spectralSet lam)
    (hS0 : ∀ u∈U, spectralS (zeta u)≠0)
    (hB : ∀ u∈U, B u= -spectralT lam (zeta u)/spectralS (zeta u))
    (hS : ∀ u∈U, S u=spectralS (zeta u))
    (he : ∀ u∈U, edgeMapV lam (-1) (zeta u)=(b : ℂ)+u)
    (hup : ∀ u∈U, 0<u.im) (hBi : ∀ u∈U, 0<(B u).im)
    (hp : Tendsto path l (𝓝 0)) (hin : ∀ᶠ t in l, path t∈U) (j : ℕ) :
    ∃ G : ℕ → ℝ, Summable G ∧ ∀ᶠ t in l, ∀ n : ℕ,
      ‖iteratedDeriv j (negativeShiftedPeriod b B (fun v => S v/A v) (2*n)) (path t)‖≤G n := by
  have hlim (n : ℕ) := fixed_odd_scaledNegativePeriod_boundary_jets (2*n)
    (show Odd (2*n+1) from ⟨n,by omega⟩) hzeta hAa0 hU hSedge hedge hb hBedge
      hB hS he hup hBi hp hin j
  obtain ⟨δ,hδ,G,hG,hbound⟩ := scaledNegativeShiftedPeriod_summable_jet_majorant_upper
    hb hB0 hBa hSa hSzero hAa0 hA0 hU ha hAa hz hS0 hB hS he hup hBi j
  have hi : Function.Injective (fun k : ℕ => 2*k+1) := by
    intro a b h
    dsimp only at h
    omega
  apply exists_summable_bound_of_summable_tail (j+2) (hG.comp_injective hi) hlim
  have heps : ∀ᶠ t in l, ‖path t‖<δ := by
    exact hp.norm.eventually (gt_mem_nhds (by simpa only [norm_zero] using hδ))
  filter_upwards [hin,heps] with t hu hε k
  have hh := hbound (path t) (hup _ hu) hε hu (2*k+1)
  have hn : 2*j+3+(2*k+1)=2*(k+(j+2)) := by omega
  simpa only [hn,Function.comp_apply] using hh

end
end IsingBulk.Anisotropic.NegativeDominance
