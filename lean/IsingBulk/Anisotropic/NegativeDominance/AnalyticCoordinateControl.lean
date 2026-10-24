import IsingBulk.Anisotropic.NegativeDominance.BoundaryJetsComposition
import Mathlib.Analysis.Calculus.MeanValue

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Set Filter Metric
open scoped Topology

theorem analytic_zero_uniform_linear_bound {f : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hf0 : f 0=0) :
    ∃ δ L : ℝ, 0<δ ∧ 0<L ∧ ∀ u : ℂ, ‖u‖<δ →
      AnalyticAt ℂ f u ∧ ‖f u‖≤L*‖u‖ := by
  obtain ⟨L,hL,hbound⟩ := analytic_finite_jets_uniform_bound hf 1
  have he : ∀ᶠ u in 𝓝 (0 : ℂ), AnalyticAt ℂ f u ∧ ‖deriv f u‖≤L := by
    filter_upwards [hf.eventually_analyticAt,hbound] with u hu hj
    refine ⟨hu,?_⟩
    simpa using hj 1 le_rfl le_rfl
  obtain ⟨δ,hδ,hδsub⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨δ,L,hδ,hL,?_⟩
  intro u hu
  have huδ : u∈ball 0 δ := by simpa only [mem_ball,dist_zero_right] using hu
  refine ⟨(hδsub huδ).1,?_⟩
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun v hv => (hδsub hv).1.differentiableAt) (fun v hv => (hδsub hv).2)
    (convex_ball (0 : ℂ) δ) (mem_ball_self hδ) huδ
  simpa only [hf0,sub_zero] using hh

end
end IsingBulk.Anisotropic.NegativeDominance
