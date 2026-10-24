import IsingBulk.Anisotropic.RegularEdges.PositiveIntegratedCoefficient
import IsingBulk.Anisotropic.NegativeDominance.ParticleWeightScaling
import IsingBulk.Anisotropic.NegativeDominance.WeightedAngularJets

noncomputable section
open IsingBulk.First IsingBulk.HT.Contour IsingBulk.Anisotropic.NegativeDominance
open Set Filter MeasureTheory
open scoped Topology
namespace IsingBulk.Anisotropic.RegularEdges

theorem scaledPositiveCoefficient_iteratedDeriv (n j : ℕ)
    {lam b : ℝ} {B S A zeta : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (ha : AnalyticOnNhd ℂ zeta U) (hAa : AnalyticOnNhd ℂ A U)
    (hz : ∀u∈U, zeta u∉spectralSet lam) (hs : ∀u∈U, spectralS (zeta u)≠0)
    (hB : ∀u∈U, B u=spectralT lam (zeta u)/spectralS (zeta u))
    (hS : ∀u∈U, S u=spectralS (zeta u))
    (he : ∀u∈U, edgeMapV lam 1 (zeta u)=(b:ℂ)+u)
    (hup : ∀u∈U, 0<u.im) (hBi : ∀u∈U, 0<(B u).im) {u : ℂ} (hu : u∈U) :
    iteratedDeriv j (fun v => (A v)^(n+1)*unscaledAngularCoefficient n lam (zeta v)) u =
      ((n+1).factorial:ℂ)⁻¹ * ∫ q : Fin n → ℝ,
        iteratedDeriv j (fun v => edgeFullIntegrand b B (fun w => S w/A w) v
          (centeredFullAngles n q)) u ∂Measure.pi (fun _ => edgeAngleMeasure) := by
  let K : Set (Fin n → ℝ) := Icc (fun _ => -Real.pi) (fun _ => Real.pi)
  let Q : (Fin n → ℝ) → (Fin (n+1) → ℝ) := physicalDependentAngles n
  let C : ℂ := ((n+1).factorial:ℂ)⁻¹*((2*Real.pi:ℂ)⁻¹)^n
  have hd (v : ℂ) (hv : v∈U) (q : Fin n → ℝ) :
      (A v)^(n+1)*complexAngularDensity lam (zeta v) (fun i => (Q q i:ℂ)) =
      edgeFullIntegrand b B (fun w => S w/A w) v (centeredFullAngles n q) := by
    rw [edgeFullIntegrand_div_scale]
    congr 1
    rw [←complexAngularDensity_wrapAngle lam (zeta v) (Q q)]
    exact complexAngularDensity_eq_edgeFullIntegrand (by omega) (hz v hv) (hs v hv)
      (hB v hv) (hS v hv) (he v hv) (hup v hv) (hBi v hv) _
  have hper : (fun v => (A v)^(n+1)*unscaledAngularCoefficient n lam (zeta v)) =ᶠ[𝓝 u]
      (fun v => ∫ q in K, C*((A v)^(n+1)*complexAngularDensity lam (zeta v)
        (fun i => (Q q i:ℂ)))) := by
    filter_upwards [hU.mem_nhds hu] with v hv
    rw [unscaledAngularCoefficient_eq_centered n (hz v hv) (hs v hv),integral_const_mul,integral_const_mul]
    dsimp [C,K,Q]
    ring
  rw [hper.iteratedDeriv_eq j,
    weightedAngularDensity_integral_iteratedDeriv (K:=K) (mu:=volume)
      (W:=fun v => (A v)^(n+1)) isCompact_Icc (by omega : 0<n+1) Q
      (physicalDependentAngles_continuous n) hU ha (fun v hv => (hAa v hv).pow (n+1)) hz hs C j hu]
  have hdj (q : Fin n → ℝ) :
      iteratedDeriv j (fun v => (A v)^(n+1)*complexAngularDensity lam (zeta v) (fun i => (Q q i:ℂ))) u =
      iteratedDeriv j (fun v => edgeFullIntegrand b B (fun w => S w/A w) v (centeredFullAngles n q)) u := by
    apply Filter.EventuallyEq.iteratedDeriv_eq
    filter_upwards [hU.mem_nhds hu] with v hv using hd v hv q
  simp_rw [hdj]
  rw [integral_const_mul,edgeAngleMeasure_integral_eq]
  dsimp [C,K]
  ring

end IsingBulk.Anisotropic.RegularEdges
