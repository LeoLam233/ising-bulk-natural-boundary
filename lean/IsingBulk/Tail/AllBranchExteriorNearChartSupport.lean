import IsingBulk.Tail.AllBranchExteriorChartCutoffJets

namespace IsingBulk.Tail
noncomputable section
open Set IsingBulk.Jets

theorem allBranchExterior_near_chart_support {N : ℕ} (θ η α δ h b ρ : ℝ)
    (hδ : 0 < δ) (hh : 0 < h) (hb : 0 < b) (hρ : 0 < ρ) (v : Fin N)
    (u : Fin N → ℝ) (hu : u ∈ tsupport (allBranchExteriorNearChartWeight N θ η α δ h b ρ hδ v)) :
    (∀ i, |u i| ≤ h) ∧ b/2 ≤ |u v| ∧ branchShapeRadius u ≤ 2*ρ ∧
      allBranchExteriorDiameter u ≤ 4*ρ := by
  have hchart := allBranchChartWeight_tsupport θ η α δ h hδ hh (tsupport_mul_subset_left hu)
  have hnear : u ∈ tsupport (microExteriorNearWeight b ρ v) := tsupport_mul_subset_right hu
  have hanchor := microExteriorAnchor_jet_support hb v [] (tsupport_mul_subset_left hnear)
  have hshape := branch_near_jet_support hρ [] (tsupport_mul_subset_right hnear)
  change branchShapeRadius u ≤ 2*ρ at hshape
  refine ⟨hchart,hanchor,hshape,?_⟩
  linarith [allBranchExterior_diameter_shape_upper u]

theorem allBranchExterior_near_chart_common_sign {N : ℕ} (θ η α δ h b ρ : ℝ)
    (hδ : 0 < δ) (hh : 0 < h) (hb : 0 < b) (hρ : 0 < ρ) (hscale : 2*ρ ≤ b/8)
    (v : Fin N) (u : Fin N → ℝ)
    (hu : u ∈ tsupport (allBranchExteriorNearChartWeight N θ η α δ h b ρ hδ v)) :
    (∀ i, b/4 ≤ u i) ∨ (∀ i, u i ≤ -(b/4)) := by
  have hs := allBranchExterior_near_chart_support θ η α δ h b ρ hδ hh hb hρ v u hu
  exact (near_equality_anchor_common_sign u v hb hs.2.1 (hs.2.2.1.trans hscale)).imp And.right And.right

end
end IsingBulk.Tail
