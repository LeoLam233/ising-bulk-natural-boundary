import IsingBulk.Anisotropic.NegativeDominance.NegativeJetMajorant
import IsingBulk.Anisotropic.NegativeDominance.NegativePeriodBoundary
import IsingBulk.Anisotropic.NegativeDominance.TailTannery

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.Anisotropic.RegularEdges Set Filter
open scoped Topology

/-- Boundary passage for the complete odd sum of actual negative-period jets.
There is no finite-index replacement and no assumed uniform jet majorant:
the summable tail is derived from the full angular density estimates. -/
theorem complete_odd_negativePeriod_boundary_jets
    {lam b : ℝ} {B S zeta : ℂ → ℂ} {U : Set ℂ}
    (hb : |b|<1) (hB0 : 0<(B 0).im) (hBa : AnalyticAt ℂ B 0)
    (hSa : AnalyticAt ℂ S 0) (hSzero : S 0≠0)
    (hzeta : AnalyticAt ℂ zeta 0)
    (hSedge : spectralS (zeta 0)≠0)
    (hedge : spectralA lam (zeta 0)+spectralT lam (zeta 0)=(b : ℂ)*spectralS (zeta 0))
    (hBedge : 0<(-spectralT lam (zeta 0)/spectralS (zeta 0)).im)
    (hU : IsOpen U) (ha : AnalyticOnNhd ℂ zeta U)
    (hz : ∀ u∈U, zeta u∉spectralSet lam)
    (hS0 : ∀ u∈U, spectralS (zeta u)≠0)
    (hB : ∀ u∈U, B u= -spectralT lam (zeta u)/spectralS (zeta u))
    (hS : ∀ u∈U, S u=spectralS (zeta u))
    (he : ∀ u∈U, edgeMapV lam (-1) (zeta u)=(b : ℂ)+u)
    (hup : ∀ u∈U, 0<u.im) (hBi : ∀ u∈U, 0<(B u).im)
    (hin : ∀ᶠ ε : ℝ in 𝓝[>] 0, Complex.I*(ε : ℂ)∈U) (j : ℕ) :
    Tendsto (fun ε : ℝ => ∑' n : ℕ,
      iteratedDeriv j (negativeShiftedPeriod b B S (2*n)) (Complex.I*(ε : ℂ)))
      (𝓝[>] 0)
      (𝓝 (∑' n : ℕ, iteratedDeriv j
        (fun u => continuedAngularCoefficient (2*n) lam (zeta u)) 0)) := by
  have hp : Tendsto (fun ε : ℝ => Complex.I*(ε : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun ε : ℝ => Complex.I*(ε : ℂ)) := by fun_prop
    simpa only [Complex.ofReal_zero,mul_zero] using
      (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hlim (n : ℕ) := fixed_odd_negativePeriod_boundary_jets (2*n)
    (show Odd (2*n+1) from ⟨n,by omega⟩) hzeta hU hSedge hedge hb hBedge
      hB hS he hup hBi hp hin j
  obtain ⟨δ,hδ,G,hG,hbound⟩ := negativeShiftedPeriod_summable_jet_majorant
    hb hB0 hBa hSa hSzero hU ha hz hS0 hB hS he hup hBi j
  have hi : Function.Injective (fun k : ℕ => 2*k+1) := by
    intro a b h
    dsimp only at h
    omega
  apply tendsto_tsum_of_summable_tail (j+2) (hG.comp_injective hi) hlim
  have heps : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0<ε ∧ ε<δ := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with ε hε heδ
    exact ⟨hε,heδ⟩
  filter_upwards [hin,heps] with ε hu hε k
  have hh := hbound ε hε.1 hε.2 hu (2*k+1)
  have hn : 2*j+3+(2*k+1)=2*(k+(j+2)) := by omega
  simpa only [hn,Function.comp_apply] using hh

/-- Absolute convergence of the complete limiting boundary jet series. -/
theorem complete_odd_negativePeriod_boundary_jets_norm_summable
    {lam b : ℝ} {B S zeta : ℂ → ℂ} {U : Set ℂ}
    (hb : |b|<1) (hB0 : 0<(B 0).im) (hBa : AnalyticAt ℂ B 0)
    (hSa : AnalyticAt ℂ S 0) (hSzero : S 0≠0)
    (hzeta : AnalyticAt ℂ zeta 0)
    (hSedge : spectralS (zeta 0)≠0)
    (hedge : spectralA lam (zeta 0)+spectralT lam (zeta 0)=(b : ℂ)*spectralS (zeta 0))
    (hBedge : 0<(-spectralT lam (zeta 0)/spectralS (zeta 0)).im)
    (hU : IsOpen U) (ha : AnalyticOnNhd ℂ zeta U)
    (hz : ∀ u∈U, zeta u∉spectralSet lam)
    (hS0 : ∀ u∈U, spectralS (zeta u)≠0)
    (hB : ∀ u∈U, B u= -spectralT lam (zeta u)/spectralS (zeta u))
    (hS : ∀ u∈U, S u=spectralS (zeta u))
    (he : ∀ u∈U, edgeMapV lam (-1) (zeta u)=(b : ℂ)+u)
    (hup : ∀ u∈U, 0<u.im) (hBi : ∀ u∈U, 0<(B u).im)
    (hin : ∀ᶠ ε : ℝ in 𝓝[>] 0, Complex.I*(ε : ℂ)∈U) (j : ℕ) :
    Summable (fun n : ℕ => ‖iteratedDeriv j
      (fun u => continuedAngularCoefficient (2*n) lam (zeta u)) 0‖) := by
  have hp : Tendsto (fun ε : ℝ => Complex.I*(ε : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun ε : ℝ => Complex.I*(ε : ℂ)) := by fun_prop
    simpa only [Complex.ofReal_zero,mul_zero] using
      (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  have hlim (n : ℕ) := fixed_odd_negativePeriod_boundary_jets (2*n)
    (show Odd (2*n+1) from ⟨n,by omega⟩) hzeta hU hSedge hedge hb hBedge
      hB hS he hup hBi hp hin j
  obtain ⟨δ,hδ,G,hG,hbound⟩ := negativeShiftedPeriod_summable_jet_majorant
    hb hB0 hBa hSa hSzero hU ha hz hS0 hB hS he hup hBi j
  have hi : Function.Injective (fun k : ℕ => 2*k+1) := by
    intro a b h
    dsimp only at h
    omega
  apply summable_of_summable_tail_limit (j+2) (hG.comp_injective hi) hlim
  have heps : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0<ε ∧ ε<δ := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds] with ε hε heδ
    exact ⟨hε,heδ⟩
  filter_upwards [hin,heps] with ε hu hε k
  have hh := hbound ε hε.1 hε.2 hu (2*k+1)
  have hn : 2*j+3+(2*k+1)=2*(k+(j+2)) := by omega
  simpa only [hn,Function.comp_apply] using hh

end
end IsingBulk.Anisotropic.NegativeDominance
