import IsingBulk.Anisotropic.NegativeDominance.ScaledPeriodBoundary
import IsingBulk.Joint.Negative.UpperPeriod
import IsingBulk.Joint.Negative.CanonicalJets

namespace IsingBulk.Joint.Negative
noncomputable section
open IsingBulk.Anisotropic IsingBulk.Anisotropic.NegativeDominance
open IsingBulk.Anisotropic.RegularEdges Set Filter
open scoped Topology

/-- Every fixed odd shifted period has genuine inward boundary jets. The
boundary values come from the continued literal finite-particle integral. -/
theorem fixed_odd_scaledNegativePeriod_boundary_jets
    {ι : Type*} {l : Filter ι} {path : ι → ℂ}
    (n : ℕ) (hN : Odd (n+1)) {b : ℝ} {B S amp : ℂ→ℂ} {curve : ℂ→Coupling} {U : Set ℂ}
    (hcurve : AnalyticAt ℂ curve 0) (hAa : AnalyticAt ℂ amp 0) (hU : IsOpen U)
    (hSzero : IsingBulk.Joint.S (curve 0)≠0)
    (hedge : IsingBulk.Joint.A (curve 0)+T (curve 0)=(b : ℂ)*IsingBulk.Joint.S (curve 0))
    (hb : |b|<1) (hBzero : 0<(-T (curve 0)/IsingBulk.Joint.S (curve 0)).im)
    (hB : ∀ u∈U, B u= -T (curve u)/IsingBulk.Joint.S (curve u))
    (hS : ∀ u∈U, S u=IsingBulk.Joint.S (curve u))
    (he : ∀ u∈U, transferC (curve u)+transferB (curve u)=(b : ℂ)+u)
    (hup : ∀ u∈U, 0<u.im) (hBi : ∀ u∈U, 0<(B u).im)
    (hp : Tendsto path l (𝓝 0)) (hin : ∀ᶠ t in l, path t∈U) (j : ℕ) :
    Tendsto (fun t => iteratedDeriv j (negativeShiftedPeriod b B (fun v => S v/amp v) n) (path t)) l
      (𝓝 (iteratedDeriv j (fun u => (amp u)^(n+1)*continuedAngularCoefficient n (curve u)) 0)) := by
  have ha : AnalyticAt ℂ (fun u => (amp u)^(n+1)*continuedAngularCoefficient n (curve u)) 0 :=
    weighted_coefficient_negative_analyticAt n hN hcurve hAa hSzero hedge hb hBzero
  have hc : ContinuousAt (iteratedDeriv j (fun u => (amp u)^(n+1)*continuedAngularCoefficient n (curve u))) 0 := by
    simpa only [iteratedDeriv_eq_iterate] using (ha.iterated_deriv j).continuousAt
  apply (hc.tendsto.comp hp).congr'
  filter_upwards [hin] with t ht
  have hh : negativeShiftedPeriod b B (fun v => S v/amp v) n =ᶠ[𝓝 (path t)]
      (fun u => (amp u)^(n+1)*continuedAngularCoefficient n (curve u)) := by
    filter_upwards [hU.mem_nhds ht] with u hu
    rw [negativeShiftedPeriod_div_scale]
    rw [continuedAngularCoefficient_eq_negativeShiftedPeriod n (hB u hu) (hS u hu)
      (he u hu) (hup u hu) (hBi u hu)]
  exact (hh.iteratedDeriv_eq j).symm

end
end IsingBulk.Joint.Negative
