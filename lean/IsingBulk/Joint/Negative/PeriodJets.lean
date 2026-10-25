import IsingBulk.Joint.Negative.WeightedJets
import IsingBulk.Anisotropic.NegativeDominance.ScaledPeriodJets
import IsingBulk.Joint.Negative.UpperPeriod
import IsingBulk.Joint.Negative.CanonicalJets

namespace IsingBulk.Joint.Negative
noncomputable section
open IsingBulk.Anisotropic IsingBulk.Anisotropic.NegativeDominance
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour IsingBulk.Anisotropic.RegularEdges
open Set MeasureTheory Filter
open scoped BigOperators Topology

/-- All derivative exchanges for the genuine negative shifted period, proved
from the literal joint analytic density on a physical chart. -/
theorem scaledNegativeShiftedPeriod_iteratedDeriv (n j : ℕ)
    {b : ℝ} {B S amp : ℂ→ℂ} {curve : ℂ→Coupling} {U : Set ℂ} (hU : IsOpen U)
    (ha : AnalyticOnNhd ℂ curve U) (hAa : AnalyticOnNhd ℂ amp U) (hz : ∀ u∈U, curve u∉spectralSet)
    (hS0 : ∀ u∈U, IsingBulk.Joint.S (curve u)≠0)
    (hB : ∀ u∈U, B u= -T (curve u)/IsingBulk.Joint.S (curve u))
    (hS : ∀ u∈U, S u=IsingBulk.Joint.S (curve u))
    (he : ∀ u∈U, transferC (curve u)+transferB (curve u)=(b : ℂ)+u)
    (hup : ∀ u∈U, 0<u.im) (hBi : ∀ u∈U, 0<(B u).im)
    {u : ℂ} (hu : u∈U) :
    iteratedDeriv j (negativeShiftedPeriod b B (fun v => S v/amp v) n) u=
      ((n+1).factorial : ℂ)⁻¹*(-1 : ℂ)^((n+1).choose 2)*
        ∫ q : Fin n → ℝ, iteratedDeriv j
          (fun v => negativeShiftedFullIntegrand b B (fun v => S v/amp v) n v q) u
            ∂Measure.pi (fun _ => edgeAngleMeasure) := by
  let K : Set (Fin n → ℝ) := Icc (fun _ => -Real.pi) (fun _ => Real.pi)
  let Q : (Fin n → ℝ) → (Fin (n+1) → ℝ) :=
    fun q => physicalDependentAngles n (fun i => q i+Real.pi)
  let C : ℂ := ((n+1).factorial : ℂ)⁻¹*((2*Real.pi : ℂ)⁻¹)^n
  let sign : ℂ := (-1 : ℂ)^((n+1).choose 2)
  have hQ : Continuous Q := (physicalDependentAngles_continuous n).comp
    (continuous_pi (fun i => (continuous_apply i).add continuous_const))
  have hd (v : ℂ) (hv : v∈U) (q : Fin n → ℝ) :
      ((amp v)^(n+1)*complexAngularDensity (curve v) (fun i => (Q q i : ℂ)))=
        sign*negativeShiftedFullIntegrand b B (fun v => S v/amp v) n v q := by
    rw [negativeShiftedFullIntegrand_div_scale,
      complexAngularDensity_eq_negativeShiftedFullIntegrand n (hB v hv) (hS v hv)
        (he v hv) (hup v hv) (hBi v hv)]
    ring

  have hper : negativeShiftedPeriod b B (fun v => S v/amp v) n =ᶠ[𝓝 u]
      (fun v => ∫ q in K, C*((amp v)^(n+1)*complexAngularDensity (curve v) (fun i => (Q q i : ℂ)))) := by
    filter_upwards [hU.mem_nhds hu] with v hv
    simp_rw [hd v hv]
    rw [integral_const_mul,integral_const_mul]
    unfold negativeShiftedPeriod
    rw [edgeAngleMeasure_integral_eq]
    dsimp [C,K,sign]
    ring
  rw [hper.iteratedDeriv_eq j]
  rw [weightedAngularDensity_integral_iteratedDeriv (K := K) (mu := volume)
    (W := fun v => (amp v)^(n+1)) isCompact_Icc
    (by omega : 0<n+1) Q hQ hU ha (fun v hv => (hAa v hv).pow (n+1)) hz hS0 C j hu]
  have hdj (q : Fin n → ℝ) :
      iteratedDeriv j (fun v => ((amp v)^(n+1)*complexAngularDensity (curve v) (fun i => (Q q i : ℂ)))) u=
        sign*iteratedDeriv j (fun v => negativeShiftedFullIntegrand b B (fun v => S v/amp v) n v q) u := by
    have hh : (fun v => ((amp v)^(n+1)*complexAngularDensity (curve v) (fun i => (Q q i : ℂ)))) =ᶠ[𝓝 u]
        (fun v => sign*negativeShiftedFullIntegrand b B (fun v => S v/amp v) n v q) := by
      filter_upwards [hU.mem_nhds hu] with v hv using hd v hv q
    rw [hh.iteratedDeriv_eq j,iteratedDeriv_const_mul_field]
  simp_rw [hdj]
  rw [integral_const_mul,integral_const_mul,edgeAngleMeasure_integral_eq]
  dsimp [C,K,sign]
  ring

end
end IsingBulk.Joint.Negative
