import IsingBulk.Joint.Negative.CompactFamilies

/-! A common source ball and an OPEN parameter neighborhood of a compact
family. This is used in the actual augmented-map inverse-function construction;
it is stronger than a tube only over the compact parameter set itself. -/
namespace IsingBulk.Joint.Transverse
noncomputable section
open Set Filter Metric
open scoped Topology

/-- The compact product tube can be thickened in the parameter direction,
while retaining one positive radius before every parameter. -/
theorem compact_product_open_tube {X E : Type*} [NormedAddCommGroup X]
    [TopologicalSpace E] {Q : Set E} {U : Set (X × E)}
    (hQ : IsCompact Q) (hU : IsOpen U) (hcenter : ∀eta∈Q,(0,eta)∈U) :
    ∃r : ℝ,0<r ∧ ∃V : Set E,IsOpen V ∧ Q⊆V ∧ ball (0:X) r ×ˢ V⊆U := by
  obtain ⟨W,V,hW,hV,h0,hQV,hWV⟩ := generalized_tube_lemma
    (isCompact_singleton (x:=(0:X))) hQ hU (by
      rintro ⟨x,eta⟩ ⟨hx,heta⟩
      have hx0 : x=0 := mem_singleton_iff.mp hx
      subst x
      exact hcenter eta heta)
  have hz : (0:X)∈W := h0 (mem_singleton 0)
  obtain ⟨r,hr,hrW⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hz)
  exact ⟨r,hr,V,hV,hQV,fun _ h=>hWV ⟨hrW h.1,h.2⟩⟩

/-- The norm formulation avoids subsequent product-ball coercion bookkeeping. -/
theorem compact_product_open_norm_tube {X E : Type*} [NormedAddCommGroup X]
    [TopologicalSpace E] {Q : Set E} {U : Set (X × E)}
    (hQ : IsCompact Q) (hU : IsOpen U) (hcenter : ∀eta∈Q,(0,eta)∈U) :
    ∃r : ℝ,0<r ∧ ∃V : Set E,IsOpen V ∧ Q⊆V ∧
      ∀eta∈V,∀x : X,‖x‖<r → (x,eta)∈U := by
  obtain ⟨r,hr,V,hV,hQV,ht⟩ := compact_product_open_tube hQ hU hcenter
  refine ⟨r,hr,V,hV,hQV,?_⟩
  intro eta heta x hx
  exact ht ⟨by simpa only [mem_ball,dist_zero_right] using hx,heta⟩

end
end IsingBulk.Joint.Transverse
