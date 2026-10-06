import IsingBulk.Tail.AllBranchExteriorChartCutoffJets

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets Set
open scoped ContDiff

def allBranchExteriorFarChartWeight (N : ℕ) (θ η α δ h b ρ : ℝ) (hδ : 0 < δ)
    (q : Fin N) (u : Fin N → ℝ) : ℝ :=
  allBranchChartWeight N θ η α δ h hδ u*microExteriorFarWeight b ρ q u

def allBranchExteriorFarChartJetCost (J N : ℕ) (C₀ C₁ K b ρ : ℝ) : ℝ :=
  (2:ℝ)^J*C₀^N*((2:ℝ)^J*(C₁^N*(b⁻¹)^J)*(K*(1+24*N)^J))*(ρ⁻¹)^J

theorem allBranchExteriorFarChartWeight_smooth (N : ℕ) (θ η α δ h b ρ : ℝ)
    (hδ : 0 < δ) (q : Fin N) : ContDiff ℝ ∞ (allBranchExteriorFarChartWeight N θ η α δ h b ρ hδ q) :=
  (allBranchChartWeight_smooth N θ η α δ h hδ).mul
    ((microExteriorAnchor_smooth b q).mul (branch_shape_cutoffs_smooth ρ).1)

theorem allBranchExterior_far_chart_cutoff_jets (θ η α δ h : ℝ) (hδ : 0 < δ)
    (hθ : 0 < θ) (hθπ : θ < Real.pi) (hα : 0 < α) (hh : 0 < h)
    (hhθ : h ≤ θ/2) (hhπ : h ≤ (Real.pi-θ)/2) (J : ℕ) :
    ∃ C₀ C₁ K : ℝ, 1 ≤ C₀ ∧ 1 ≤ C₁ ∧ 1 ≤ K ∧ ∀ (N : ℕ) (b ρ : ℝ),
      0 < b → b ≤ 1 → 0 < ρ → ρ ≤ 1 → ∀ (q : Fin N) (u : Fin N → ℝ),
      0 < allBranchExteriorDiameter u → allBranchExteriorDiameter u ≤ 1 →
      ∀ l : List (Fin N), l.length ≤ J →
      ‖cutoffJet l (allBranchExteriorFarChartWeight N θ η α δ h b ρ hδ q) u‖ ≤
        allBranchExteriorFarChartJetCost J N C₀ C₁ K b ρ/allBranchExteriorDiameter u^l.length := by
  obtain ⟨C₀,hC₀,hchart⟩ := allBranchChartWeight_jet_bound θ η α δ h hδ hθ hθπ hα hh hhθ hhπ J
  obtain ⟨C₁,K,hC₁,hK,hexterior⟩ := microExteriorNearFar_sharp_jet_bound J
  refine ⟨C₀,C₁,K,hC₀,hC₁,hK,?_⟩
  intro N b ρ hb hb1 hρ hρ1 q u hdiam hdiam1 l hl
  have hgj (k : List (Fin N)) (hk : k.length ≤ J) :
      ‖cutoffJet k (microExteriorFarWeight b ρ q) u‖ ≤
        ((2:ℝ)^J*(C₁^N*(b⁻¹)^J)*(K*(1+24*N)^J))*(ρ⁻¹)^k.length := by
    simpa only [mul_assoc] using (hexterior N b ρ hb hb1 hρ hρ1 q u k hk).2
  have hh := cutoffJet_product_scale_bound (allBranchChartWeight N θ η α δ h hδ)
    (microExteriorFarWeight b ρ q) (allBranchChartWeight_smooth N θ η α δ h hδ)
    ((microExteriorAnchor_smooth b q).mul (branch_shape_cutoffs_smooth ρ).1) u
    (by positivity) (by positivity) hρ hρ1 (fun k hk => hchart N k hk u) hgj l hl
  have hW : 0 ≤ allBranchExteriorFarChartJetCost J N C₀ C₁ K b ρ := by
    unfold allBranchExteriorFarChartJetCost
    positivity
  have hbnd : ‖cutoffJet l (allBranchExteriorFarChartWeight N θ η α δ h b ρ hδ q) u‖ ≤
      allBranchExteriorFarChartJetCost J N C₀ C₁ K b ρ := by
    apply hh.trans
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ((one_le_inv₀ hρ).mpr hρ1) hl) (by positivity)
  exact hbnd.trans ((le_div_iff₀ (pow_pos hdiam _)).mpr
    (mul_le_of_le_one_right hW (pow_le_one₀ hdiam.le hdiam1)))

theorem allBranchExterior_diameter_cube_bound {N : ℕ} (u : Fin N → ℝ) (h : ℝ)
    (hh : 0 ≤ h) (hu : ∀ i, |u i| ≤ h) : allBranchExteriorDiameter u ≤ 2*h := by
  by_cases hd : 0 < allBranchExteriorDiameter u
  · obtain ⟨p,q,_,he⟩ := allBranchExterior_diameter_attained u hd
    rw [← he]
    exact (abs_sub (u p) (u q)).trans (by linarith [hu p,hu q])
  · linarith

theorem allBranchExterior_far_chart_support {N : ℕ} (θ η α δ h b ρ : ℝ)
    (hδ : 0 < δ) (hh : 0 < h) (hb : 0 < b) (hρ : 0 < ρ) (v : Fin N)
    (u : Fin N → ℝ) (hu : u ∈ tsupport (allBranchExteriorFarChartWeight N θ η α δ h b ρ hδ v)) :
    (∀ i, |u i| ≤ h) ∧ b/2 ≤ |u v| ∧ ρ ≤ branchShapeRadius u ∧
      allBranchExteriorDiameter u ≤ 2*h := by
  have hchart := allBranchChartWeight_tsupport θ η α δ h hδ hh (tsupport_mul_subset_left hu)
  have hfar : u ∈ tsupport (microExteriorFarWeight b ρ v) := tsupport_mul_subset_right hu
  exact ⟨hchart,microExteriorAnchor_jet_support hb v [] (tsupport_mul_subset_left hfar),
    branch_far_jet_support hρ [] (tsupport_mul_subset_right hfar),
    allBranchExterior_diameter_cube_bound u h hh.le hchart⟩

end
end IsingBulk.Tail
