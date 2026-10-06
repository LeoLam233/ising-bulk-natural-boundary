import IsingBulk.First.CompactParameterIntegral
import IsingBulk.First.PoleDifferentiation

/-! All-order compact integration for literal parameter jets with joint
continuity. No derivative estimate is included as an assumed conclusion. -/
namespace IsingBulk.First
noncomputable section
open Set Filter MeasureTheory
open scoped Topology

theorem analytic_iterate_deriv_at {F : ℂ → ℂ} {s : ℂ} (hF : AnalyticAt ℂ F s) (k : ℕ) :
    AnalyticAt ℂ (deriv^[k] F) s := by
  induction k with
  | zero => exact hF
  | succ k ih =>
    simpa only [Function.iterate_succ',Function.comp_apply] using ih.deriv

theorem compact_joint_jet_integral_iteratedDeriv
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {K : Set X} (hK : IsCompact K)
    {U : Set ℂ} (hU : IsOpen U) (H : ℕ → ℂ → X → ℂ)
    (hc : ∀ j, ContinuousOn (fun p : ℂ × X => H j p.1 p.2) (U ×ˢ K))
    (hd : ∀ j s, s ∈ U → ∀ x ∈ K, HasDerivAt (fun z => H j z x) (H (j+1) s x) s)
    (k : ℕ) : ∀ s ∈ U,
      (deriv^[k] (fun z => ∫ x in K, H 0 z x ∂μ)) s = ∫ x in K, H k s x ∂μ := by
  induction k with
  | zero => intro s hs; rfl
  | succ k ih =>
    intro s hs
    rw [Function.iterate_succ',Function.comp_apply]
    have heq : (deriv^[k] (fun z => ∫ x in K, H 0 z x ∂μ)) =ᶠ[𝓝 s]
        (fun z => ∫ x in K, H k z x ∂μ) :=
      (show ∀ᶠ z in 𝓝 s, z ∈ U from hU.mem_nhds hs).mono (fun z hz => ih z hz)
    rw [heq.deriv_eq]
    exact (hasDerivAt_compact_integral hK (hU.mem_nhds hs) (H k) (H (k+1)) (hc k) (hc (k+1)) (hd k)).deriv

end
end IsingBulk.First
