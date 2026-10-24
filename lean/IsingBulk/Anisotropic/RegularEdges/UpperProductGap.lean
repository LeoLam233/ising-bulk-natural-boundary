import IsingBulk.Anisotropic.RegularEdges.ProductGap
noncomputable section
open Set Filter Metric
open scoped Topology BigOperators
namespace IsingBulk.Anisotropic.RegularEdges

theorem edgeRootProduct_retained_gap_upper {b : ℝ} {B : ℂ → ℂ}
    (hB : 0<(B 0).im) (hc : ContinuousAt B 0) :
    ∃ c δ : ℝ, 0<c ∧ 0<δ ∧ ∀ v : ℂ, 0<v.im → ‖v‖<δ →
      ∀ (N m : ℕ) [Nonempty (Fin m)] (q : Fin N → ℝ) (p : Fin m → Fin N),
      (∀ i, q i∈Icc (-Real.pi) Real.pi) →
      0<c*(v.im+‖fun i => q (p i)‖^2) ∧
      c*(v.im+‖fun i => q (p i)‖^2)≤1 ∧
      c*(v.im+‖fun i => q (p i)‖^2)≤‖1-edgeRootProduct b B v q‖ := by
  obtain ⟨c,hcpos,hg⟩ := edgeParamRoot_uniform_gap (b:=b) hB hc
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hg
  refine ⟨c,δ,hcpos,hδ,?_⟩
  intro v hv hvδ N m _ q p hq
  exact root_product_retained_gap _ q p hcpos hv (fun i =>
    hball (show v∈ball (0:ℂ) δ by simpa using hvδ) (q i) (hq i) hv)

end IsingBulk.Anisotropic.RegularEdges
