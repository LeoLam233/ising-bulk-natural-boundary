import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral

/-! Differentiating a genuine compact-domain Bochner integral. Joint continuity
on a parameter neighborhood supplies the uniform integrable derivative bound. -/
namespace IsingBulk.First
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology

theorem hasDerivAt_compact_integral {A : Type*} [TopologicalSpace A] [T2Space A]
    [MeasurableSpace A] [OpensMeasurableSpace A] {μ : Measure A}
    [IsFiniteMeasureOnCompacts μ] {K : Set A} (hK : IsCompact K)
    {U : Set ℂ} {s : ℂ} (hU : U ∈ 𝓝 s)
    (F G : ℂ → A → ℂ)
    (hF : ContinuousOn (fun p : ℂ × A => F p.1 p.2) (U ×ˢ K))
    (hG : ContinuousOn (fun p : ℂ × A => G p.1 p.2) (U ×ˢ K))
    (hd : ∀ t ∈ U, ∀ a ∈ K, HasDerivAt (fun z => F z a) (G t a) t) :
    HasDerivAt (fun t => ∫ a in K, F t a ∂μ) (∫ a in K, G s a ∂μ) s := by
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
  have hsU := mem_of_mem_nhds hU
  have hball : closedBall s (ε/2) ⊆ U :=
    (closedBall_subset_ball (by linarith : ε/2 < ε)).trans hεU
  have hFc (t : ℂ) (ht : t ∈ U) : ContinuousOn (F t) K := by
    exact hF.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ ha => ⟨ht, ha⟩)
  have hGc (t : ℂ) (ht : t ∈ U) : ContinuousOn (G t) K := by
    exact hG.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ ha => ⟨ht, ha⟩)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall s (ε/2)).prod hK).exists_bound_of_continuousOn
    (hG.mono (prod_mono hball Subset.rfl))
  have hbound : Integrable (fun _a : A => C) (μ.restrict K) :=
    integrableOn_const hK.measure_lt_top.ne
  apply (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (closedBall_mem_nhds s (by linarith : 0 < ε/2))
    ((Filter.Eventually.mono hU) (fun t ht => ((hFc t ht).integrableOn_compact hK).aestronglyMeasurable))
    ((hFc s hsU).integrableOn_compact hK)
    ((hGc s hsU).integrableOn_compact hK).aestronglyMeasurable
    ?_ hbound ?_).2
  · filter_upwards [ae_restrict_mem hK.measurableSet] with a ha
    intro t ht
    exact hC (t,a) ⟨ht,ha⟩
  · filter_upwards [ae_restrict_mem hK.measurableSet] with a ha
    intro t ht
    exact hd t (hball ht) a ha

end
end IsingBulk.First
