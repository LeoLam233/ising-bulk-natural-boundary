import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Joint parameter continuity of compact source integrals with an actual
uniform integrable bound. -/
namespace IsingBulk.First
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

theorem compact_parameter_integral_continuousOn
    {P X : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {K : Set X} (hK : IsCompact K)
    {V : Set P} (F : P → X → ℂ)
    (hF : ContinuousOn (fun p : P × X => F p.1 p.2) (V ×ˢ K))
    (C : ℝ) (hB : ∀ p ∈ V, ∀ x ∈ K, ‖F p x‖ ≤ C) :
    ContinuousOn (fun p => ∫ x in K, F p x ∂μ) V := by
  intro p hp
  have hs (q : P) (hq : q ∈ V) : ContinuousOn (F q) K :=
    hF.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ hx => ⟨hq,hx⟩)
  apply tendsto_integral_filter_of_dominated_convergence (μ := μ.restrict K) (fun _ => C)
  · filter_upwards [self_mem_nhdsWithin] with q hq
    exact ((hs q hq).integrableOn_compact hK).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with q hq
    exact (ae_restrict_mem hK.measurableSet).mono (fun x hx => hB q hq x hx)
  · exact integrableOn_const hK.measure_lt_top.ne
  · filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    have hpF : ContinuousWithinAt (fun q : P => F q x) V p :=
      (hF (p,x) ⟨hp,hx⟩).comp (f := fun q : P => (q,x))
        (continuous_id.prodMk (continuous_const : Continuous (fun _ : P => x))).continuousWithinAt
        (fun q hq => ⟨hq,hx⟩)
    exact hpF

end
end IsingBulk.First
