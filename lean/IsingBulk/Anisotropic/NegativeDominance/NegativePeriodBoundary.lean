import IsingBulk.Anisotropic.NegativeDominance.NegativeShiftedPeriod
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.Anisotropic.RegularEdges Set Filter
open scoped Topology

/-- Every fixed odd shifted period has genuine inward boundary jets. The
boundary values come from the continued literal finite-particle integral. -/
theorem fixed_odd_negativePeriod_boundary_jets
    {ι : Type*} {l : Filter ι} {path : ι → ℂ}
    (n : ℕ) (hN : Odd (n+1)) {lam b : ℝ} {B S zeta : ℂ → ℂ} {U : Set ℂ}
    (hzeta : AnalyticAt ℂ zeta 0) (hU : IsOpen U)
    (hSzero : spectralS (zeta 0)≠0)
    (hedge : spectralA lam (zeta 0)+spectralT lam (zeta 0)=(b : ℂ)*spectralS (zeta 0))
    (hb : |b|<1) (hBzero : 0<(-spectralT lam (zeta 0)/spectralS (zeta 0)).im)
    (hB : ∀ u∈U, B u= -spectralT lam (zeta u)/spectralS (zeta u))
    (hS : ∀ u∈U, S u=spectralS (zeta u))
    (he : ∀ u∈U, edgeMapV lam (-1) (zeta u)=(b : ℂ)+u)
    (hup : ∀ u∈U, 0<u.im) (hBi : ∀ u∈U, 0<(B u).im)
    (hp : Tendsto path l (𝓝 0)) (hin : ∀ᶠ t in l, path t∈U) (j : ℕ) :
    Tendsto (fun t => iteratedDeriv j (negativeShiftedPeriod b B S n) (path t)) l
      (𝓝 (iteratedDeriv j (fun u => continuedAngularCoefficient n lam (zeta u)) 0)) := by
  have ha : AnalyticAt ℂ (fun u => continuedAngularCoefficient n lam (zeta u)) 0 :=
    (continuedAngularCoefficient_negative_analyticAt n hN hSzero hedge hb hBzero).comp hzeta
  have hc : ContinuousAt (iteratedDeriv j (fun u => continuedAngularCoefficient n lam (zeta u))) 0 := by
    simpa only [iteratedDeriv_eq_iterate] using (ha.iterated_deriv j).continuousAt
  apply (hc.tendsto.comp hp).congr'
  filter_upwards [hin] with t ht
  have hh : negativeShiftedPeriod b B S n =ᶠ[𝓝 (path t)]
      (fun u => continuedAngularCoefficient n lam (zeta u)) := by
    filter_upwards [hU.mem_nhds ht] with u hu
    exact (continuedAngularCoefficient_eq_negativeShiftedPeriod n (hB u hu) (hS u hu)
      (he u hu) (hup u hu) (hBi u hu)).symm
  exact (hh.iteratedDeriv_eq j).symm

end
end IsingBulk.Anisotropic.NegativeDominance
