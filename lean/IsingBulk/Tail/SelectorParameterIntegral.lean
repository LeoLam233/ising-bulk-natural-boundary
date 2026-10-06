import IsingBulk.Tail.SelectorIntegration
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral

/-! Real homotopy-parameter integration. Compactness supplies the actual
uniform derivative bound; no interchange identity is assumed. -/
namespace IsingBulk.Tail
noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff

theorem hasDerivAt_real_compact_integral {A : Type*} [TopologicalSpace A] [T2Space A]
    [MeasurableSpace A] [OpensMeasurableSpace A] {μ : Measure A}
    [IsFiniteMeasureOnCompacts μ] {K : Set A} (hK : IsCompact K)
    {U : Set ℝ} {s : ℝ} (hU : U ∈ 𝓝 s)
    (F G : ℝ → A → ℂ)
    (hF : ContinuousOn (fun p : ℝ × A => F p.1 p.2) (U ×ˢ K))
    (hG : ContinuousOn (fun p : ℝ × A => G p.1 p.2) (U ×ˢ K))
    (hd : ∀ t ∈ U, ∀ a ∈ K, HasDerivAt (fun z => F z a) (G t a) t) :
    HasDerivAt (fun t => ∫ a in K, F t a ∂μ) (∫ a in K, G s a ∂μ) s := by
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
  have hsU := mem_of_mem_nhds hU
  have hball : closedBall s (ε/2) ⊆ U :=
    (closedBall_subset_ball (by linarith : ε/2 < ε)).trans hεU
  have hFc (t : ℝ) (ht : t ∈ U) : ContinuousOn (F t) K := by
    exact hF.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ ha => ⟨ht, ha⟩)
  have hGc (t : ℝ) (ht : t ∈ U) : ContinuousOn (G t) K := by
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

 theorem compact_mass_continuousOn (N : ℕ) (F : ℝ × (Fin N → ℝ) → ℂ)
    (hc : ContinuousOn F (Icc (0:ℝ) 1 ×ˢ IsingBulk.First.angleBox N)) :
    ContinuousOn (fun t => ∫ θ in IsingBulk.First.angleBox N, F (t,θ)) (Icc (0:ℝ) 1) := by
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hc
  exact IsingBulk.First.compact_parameter_integral_continuousOn isCompact_Icc
    (fun t θ => F (t,θ)) hc C (fun t ht θ hθ => hC (t,θ) ⟨ht,hθ⟩)

 theorem compact_mass_hasDerivAt (N : ℕ) (F : ℝ × (Fin N → ℝ) → ℂ)
    (hf : ∀ t, 0 < t → ∀ θ, ContDiffAt ℝ ∞ F (t,θ)) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun u => ∫ θ in IsingBulk.First.angleBox N, F (u,θ))
      (∫ θ in IsingBulk.First.angleBox N, deriv (fun u => F (u,θ)) t) t := by
  let G : ℝ → (Fin N → ℝ) → ℂ := fun u θ => fderiv ℝ F (u,θ) (1,0)
  have hc : ContinuousOn F (Ioi (0:ℝ) ×ˢ IsingBulk.First.angleBox N) := by
    intro p hp
    exact (hf p.1 hp.1 p.2).continuousAt.continuousWithinAt
  have hG : ContinuousOn (fun p : ℝ × (Fin N → ℝ) => G p.1 p.2)
      (Ioi (0:ℝ) ×ˢ IsingBulk.First.angleBox N) := by
    intro p hp
    exact ((hf p.1 hp.1 p.2).continuousAt_fderiv (by simp)).clm_apply
      continuousAt_const |>.continuousWithinAt
  have hd : ∀ u ∈ Ioi (0:ℝ), ∀ θ ∈ IsingBulk.First.angleBox N,
      HasDerivAt (fun v => F (v,θ)) (G u θ) u := by
    intro u hu θ _
    have hp : HasDerivAt (fun v : ℝ => (v,θ)) (1,0) u := by
      convert (hasDerivAt_id u).prodMk (hasDerivAt_const u θ) using 1
      rfl
    have hh := (hf u hu θ).differentiableAt (by simp) |>.hasFDerivAt
    convert hh.comp_hasDerivAt u hp using 1
    rfl
  have hi := hasDerivAt_real_compact_integral (μ := volume) (K := IsingBulk.First.angleBox N) isCompact_Icc (Ioi_mem_nhds ht)
    (fun u θ => F (u,θ)) G hc hG hd
  convert hi using 1
  apply setIntegral_congr_fun measurableSet_Icc
  intro θ hθ
  exact (hd t ht θ hθ).deriv

 theorem compact_mass_fundamental (N : ℕ) (F : ℝ × (Fin N → ℝ) → ℂ)
    (hf : ∀ t, 0 ≤ t → ∀ θ, ContDiffAt ℝ ∞ F (t,θ)) :
    (∫ t : ℝ in 0..1, ∫ θ in IsingBulk.First.angleBox N, deriv (fun u => F (u,θ)) t) =
      (∫ θ in IsingBulk.First.angleBox N, F (1,θ)) -
      (∫ θ in IsingBulk.First.angleBox N, F (0,θ)) := by
  have hc : ContinuousOn F (Icc (0:ℝ) 1 ×ˢ IsingBulk.First.angleBox N) := by
    intro p hp
    exact (hf p.1 hp.1.1 p.2).continuousAt.continuousWithinAt
  let G : ℝ × (Fin N → ℝ) → ℂ := fun p => fderiv ℝ F p (1,0)
  have hGc : ContinuousOn G (Icc (0:ℝ) 1 ×ˢ IsingBulk.First.angleBox N) := by
    intro p hp
    exact ((hf p.1 hp.1.1 p.2).continuousAt_fderiv (by simp)).clm_apply
      continuousAt_const |>.continuousWithinAt
  have hd (t : ℝ) (ht : 0 ≤ t) (θ : Fin N → ℝ) : deriv (fun u => F (u,θ)) t=G (t,θ) := by
    have hp : HasDerivAt (fun u : ℝ => (u,θ)) (1,0) t := by
      convert (hasDerivAt_id t).prodMk (hasDerivAt_const t θ) using 1
      rfl
    have hh := (hf t ht θ).differentiableAt (by simp) |>.hasFDerivAt
    simpa only [Function.comp_def] using (hh.comp_hasDerivAt t hp).deriv
  have hJ : ContinuousOn (fun t => ∫ θ in IsingBulk.First.angleBox N,
      deriv (fun u => F (u,θ)) t) (Icc (0:ℝ) 1) := by
    apply (compact_mass_continuousOn N G hGc).congr
    intro t ht
    simp_rw [hd t ht.1]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (by norm_num)
    (compact_mass_continuousOn N F hc)
    (fun t ht => compact_mass_hasDerivAt N F (fun u hu => hf u hu.le) t ht.1)
    (hJ.intervalIntegrable_of_Icc (by norm_num))

end
end IsingBulk.Tail
