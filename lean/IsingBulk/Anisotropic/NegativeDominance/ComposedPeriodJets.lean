import IsingBulk.Anisotropic.NegativeDominance.ParticleWeightScaling
import IsingBulk.Anisotropic.NegativeDominance.WeightedAngularJets
import IsingBulk.Anisotropic.NegativeDominance.NegativeIntegratedJets
import IsingBulk.Anisotropic.RegularEdges.ComplexAngularParameterJets

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour IsingBulk.Anisotropic.RegularEdges
open Set MeasureTheory Filter
open scoped BigOperators Topology

/-- All derivative exchanges for the genuine negative shifted period, proved
from the literal joint analytic density on a physical chart. -/
theorem scaledNegativeShiftedPeriod_comp_iteratedDeriv (n j : ℕ)
    {lam b : ℝ} {B S A zeta f : ℂ → ℂ} {U V : Set ℂ} (_hU : IsOpen U)
    (ha : AnalyticOnNhd ℂ zeta U) (hAa : AnalyticOnNhd ℂ A U) (hz : ∀ u∈U, zeta u∉spectralSet lam)
    (hS0 : ∀ u∈U, spectralS (zeta u)≠0)
    (hB : ∀ u∈U, B u= -spectralT lam (zeta u)/spectralS (zeta u))
    (hS : ∀ u∈U, S u=spectralS (zeta u))
    (he : ∀ u∈U, edgeMapV lam (-1) (zeta u)=(b : ℂ)+u)
    (hup : ∀ u∈U, 0<u.im) (hBi : ∀ u∈U, 0<(B u).im)
    (hV : IsOpen V) (hf : AnalyticOnNhd ℂ f V) (hmap : MapsTo f V U)
    {u : ℂ} (hu : u∈V) :
    iteratedDeriv j (fun w => negativeShiftedPeriod b B (fun v => S v/A v) n (f w)) u=
      ((n+1).factorial : ℂ)⁻¹*(-1 : ℂ)^((n+1).choose 2)*
        ∫ q : Fin n → ℝ, iteratedDeriv j
          (fun w => negativeShiftedFullIntegrand b B (fun v => S v/A v) n (f w) q) u
            ∂Measure.pi (fun _ => edgeAngleMeasure) := by
  let K : Set (Fin n → ℝ) := Icc (fun _ => -Real.pi) (fun _ => Real.pi)
  let Q : (Fin n → ℝ) → (Fin (n+1) → ℝ) :=
    fun q => physicalDependentAngles n (fun i => q i+Real.pi)
  let C : ℂ := ((n+1).factorial : ℂ)⁻¹*((2*Real.pi : ℂ)⁻¹)^n
  let sign : ℂ := (-1 : ℂ)^((n+1).choose 2)
  have hQ : Continuous Q := (physicalDependentAngles_continuous n).comp
    (continuous_pi (fun i => (continuous_apply i).add continuous_const))
  have hd (v : ℂ) (hv : v∈V) (q : Fin n → ℝ) :
      ((A (f v))^(n+1)*complexAngularDensity lam (zeta (f v)) (fun i => (Q q i : ℂ)))=
        sign*negativeShiftedFullIntegrand b B (fun v => S v/A v) n (f v) q := by
    rw [negativeShiftedFullIntegrand_div_scale,
      complexAngularDensity_eq_negativeShiftedFullIntegrand n (hB (f v) (hmap hv)) (hS (f v) (hmap hv))
        (he (f v) (hmap hv)) (hup (f v) (hmap hv)) (hBi (f v) (hmap hv))]
    ring

  have hper : (fun v => negativeShiftedPeriod b B (fun v => S v/A v) n (f v)) =ᶠ[𝓝 u]
      (fun v => ∫ q in K, C*((A (f v))^(n+1)*complexAngularDensity lam (zeta (f v)) (fun i => (Q q i : ℂ)))) := by
    filter_upwards [hV.mem_nhds hu] with v hv
    simp_rw [hd v hv]
    rw [integral_const_mul,integral_const_mul]
    unfold negativeShiftedPeriod
    rw [edgeAngleMeasure_integral_eq]
    dsimp [C,K,sign]
    ring
  rw [hper.iteratedDeriv_eq j]
  rw [weightedAngularDensity_integral_iteratedDeriv (zeta := fun v => zeta (f v)) (K := K) (mu := volume)
    (W := fun v => (A (f v))^(n+1)) isCompact_Icc
    (by omega : 0<n+1) Q hQ hV
    (fun v hv => (ha (f v) (hmap hv)).comp (hf v hv))
    (fun v hv => ((hAa (f v) (hmap hv)).comp (hf v hv)).pow (n+1))
    (fun v hv => hz (f v) (hmap hv)) (fun v hv => hS0 (f v) (hmap hv)) C j hu]
  have hdj (q : Fin n → ℝ) :
      iteratedDeriv j (fun v => ((A (f v))^(n+1)*complexAngularDensity lam (zeta (f v)) (fun i => (Q q i : ℂ)))) u=
        sign*iteratedDeriv j (fun v => negativeShiftedFullIntegrand b B (fun v => S v/A v) n (f v) q) u := by
    have hh : (fun v => ((A (f v))^(n+1)*complexAngularDensity lam (zeta (f v)) (fun i => (Q q i : ℂ)))) =ᶠ[𝓝 u]
        (fun v => sign*negativeShiftedFullIntegrand b B (fun v => S v/A v) n (f v) q) := by
      filter_upwards [hV.mem_nhds hu] with v hv using hd v hv q
    rw [hh.iteratedDeriv_eq j,iteratedDeriv_const_mul_field]
  simp_rw [hdj]
  rw [integral_const_mul,integral_const_mul,edgeAngleMeasure_integral_eq]
  dsimp [C,K,sign]
  ring

end
end IsingBulk.Anisotropic.NegativeDominance
