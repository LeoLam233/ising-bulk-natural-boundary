import IsingBulk.Anisotropic.NegativeDominance.NegativeShiftedPeriod
import IsingBulk.Anisotropic.NegativeDominance.NegativeIntegratedJets
import IsingBulk.Anisotropic.RegularEdges.ComplexAngularParameterJets

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour IsingBulk.Anisotropic.RegularEdges
open Set MeasureTheory Filter
open scoped BigOperators Topology

/-- All derivative exchanges for the genuine negative shifted period, proved
from the literal joint analytic density on a physical chart. -/
theorem negativeShiftedPeriod_iteratedDeriv (n j : ℕ)
    {lam b : ℝ} {B S zeta : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (ha : AnalyticOnNhd ℂ zeta U) (hz : ∀ u∈U, zeta u∉spectralSet lam)
    (hS0 : ∀ u∈U, spectralS (zeta u)≠0)
    (hB : ∀ u∈U, B u= -spectralT lam (zeta u)/spectralS (zeta u))
    (hS : ∀ u∈U, S u=spectralS (zeta u))
    (he : ∀ u∈U, edgeMapV lam (-1) (zeta u)=(b : ℂ)+u)
    (hup : ∀ u∈U, 0<u.im) (hBi : ∀ u∈U, 0<(B u).im)
    {u : ℂ} (hu : u∈U) :
    iteratedDeriv j (negativeShiftedPeriod b B S n) u=
      ((n+1).factorial : ℂ)⁻¹*(-1 : ℂ)^((n+1).choose 2)*
        ∫ q : Fin n → ℝ, iteratedDeriv j
          (fun v => negativeShiftedFullIntegrand b B S n v q) u
            ∂Measure.pi (fun _ => edgeAngleMeasure) := by
  let K : Set (Fin n → ℝ) := Icc (fun _ => -Real.pi) (fun _ => Real.pi)
  let Q : (Fin n → ℝ) → (Fin (n+1) → ℝ) :=
    fun q => physicalDependentAngles n (fun i => q i+Real.pi)
  let C : ℂ := ((n+1).factorial : ℂ)⁻¹*((2*Real.pi : ℂ)⁻¹)^n
  let sign : ℂ := (-1 : ℂ)^((n+1).choose 2)
  have hQ : Continuous Q := (physicalDependentAngles_continuous n).comp
    (continuous_pi (fun i => (continuous_apply i).add continuous_const))
  have hd (v : ℂ) (hv : v∈U) (q : Fin n → ℝ) :
      complexAngularDensity lam (zeta v) (fun i => (Q q i : ℂ))=
        sign*negativeShiftedFullIntegrand b B S n v q :=
    complexAngularDensity_eq_negativeShiftedFullIntegrand n (hB v hv) (hS v hv)
      (he v hv) (hup v hv) (hBi v hv) q
  have hper : negativeShiftedPeriod b B S n =ᶠ[𝓝 u]
      (fun v => ∫ q in K, C*complexAngularDensity lam (zeta v) (fun i => (Q q i : ℂ))) := by
    filter_upwards [hU.mem_nhds hu] with v hv
    simp_rw [hd v hv]
    rw [integral_const_mul,integral_const_mul]
    unfold negativeShiftedPeriod
    rw [edgeAngleMeasure_integral_eq]
    dsimp [C,K,sign]
    ring
  rw [hper.iteratedDeriv_eq j]
  rw [complexAngularDensity_comp_integral_iteratedDeriv isCompact_Icc
    (by omega : 0<n+1) Q hQ hU ha hz hS0 C j hu]
  have hdj (q : Fin n → ℝ) :
      iteratedDeriv j (fun v => complexAngularDensity lam (zeta v) (fun i => (Q q i : ℂ))) u=
        sign*iteratedDeriv j (fun v => negativeShiftedFullIntegrand b B S n v q) u := by
    have hh : (fun v => complexAngularDensity lam (zeta v) (fun i => (Q q i : ℂ))) =ᶠ[𝓝 u]
        (fun v => sign*negativeShiftedFullIntegrand b B S n v q) := by
      filter_upwards [hU.mem_nhds hu] with v hv using hd v hv q
    rw [hh.iteratedDeriv_eq j,iteratedDeriv_const_mul_field]
  simp_rw [hdj]
  rw [integral_const_mul,integral_const_mul,edgeAngleMeasure_integral_eq]
  dsimp [C,K,sign]
  ring

end
end IsingBulk.Anisotropic.NegativeDominance
