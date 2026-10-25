import IsingBulk.Joint.Negative.CompleteBoundaryJets
import IsingBulk.Anisotropic.NegativeDominance.ScaledPeriodAllJetMajorant
import IsingBulk.Joint.Negative.UpperPeriod
import IsingBulk.Joint.Negative.CanonicalJets

namespace IsingBulk.Joint.Negative
noncomputable section
open IsingBulk.Anisotropic IsingBulk.Anisotropic.NegativeDominance
open IsingBulk.Anisotropic.RegularEdges Set Filter
open scoped Topology

/-- Genuine all-particle summable envelopes, with the finite initial indices
included by their proved continuation limits. -/
theorem scaledNegativePeriod_all_jet_majorant_upper
    {ι : Type*} {l : Filter ι} [NeBot l] {path : ι → ℂ}
    {b : ℝ} {B S amp : ℂ→ℂ} {curve : ℂ→Coupling} {U : Set ℂ}
    (hb : |b|<1) (hB0 : 0<(B 0).im) (hBa : AnalyticAt ℂ B 0)
    (hSa : AnalyticAt ℂ S 0) (hSzero : S 0≠0)
    (hAa0 : AnalyticAt ℂ amp 0) (hA0 : amp 0≠0)
    (hcurve : AnalyticAt ℂ curve 0)
    (hSedge : IsingBulk.Joint.S (curve 0)≠0)
    (hedge : IsingBulk.Joint.A (curve 0)+T (curve 0)=(b : ℂ)*IsingBulk.Joint.S (curve 0))
    (hBedge : 0<(-T (curve 0)/IsingBulk.Joint.S (curve 0)).im)
    (hU : IsOpen U) (ha : AnalyticOnNhd ℂ curve U) (hAa : AnalyticOnNhd ℂ amp U)
    (hz : ∀ u∈U, curve u∉spectralSet)
    (hS0 : ∀ u∈U, IsingBulk.Joint.S (curve u)≠0)
    (hB : ∀ u∈U, B u= -T (curve u)/IsingBulk.Joint.S (curve u))
    (hS : ∀ u∈U, S u=IsingBulk.Joint.S (curve u))
    (he : ∀ u∈U, transferC (curve u)+transferB (curve u)=(b : ℂ)+u)
    (hup : ∀ u∈U, 0<u.im) (hBi : ∀ u∈U, 0<(B u).im)
    (hp : Tendsto path l (𝓝 0)) (hin : ∀ᶠ t in l, path t∈U) (j : ℕ) :
    ∃ G : ℕ → ℝ, Summable G ∧ ∀ᶠ t in l, ∀ n : ℕ,
      ‖iteratedDeriv j (negativeShiftedPeriod b B (fun v => S v/amp v) (2*n)) (path t)‖≤G n := by
  have hlim (n : ℕ) := fixed_odd_scaledNegativePeriod_boundary_jets (2*n)
    (show Odd (2*n+1) from ⟨n,by omega⟩) hcurve hAa0 hU hSedge hedge hb hBedge
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
end IsingBulk.Joint.Negative
