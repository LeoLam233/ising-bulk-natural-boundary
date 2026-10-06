import IsingBulk.Tail.ScaledCutoffProduct
import IsingBulk.Tail.AllBranchChartJets
import IsingBulk.Tail.AllBranchExteriorEqualityGeometry

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets
open scoped ContDiff

def allBranchExteriorNearChartWeight (N : ℕ) (θ η α δ h b ρ : ℝ) (hδ : 0 < δ)
    (q : Fin N) (u : Fin N → ℝ) : ℝ :=
  allBranchChartWeight N θ η α δ h hδ u*microExteriorNearWeight b ρ q u

def allBranchExteriorNearChartJetCost (J N : ℕ) (C₀ C₁ K b : ℝ) : ℝ :=
  (2:ℝ)^J*C₀^N*((2:ℝ)^J*(C₁^N*(b⁻¹)^J)*(K*(1+24*N)^J))*(4:ℝ)^J

theorem allBranchExteriorNearChartWeight_smooth (N : ℕ) (θ η α δ h b ρ : ℝ)
    (hδ : 0 < δ) (q : Fin N) : ContDiff ℝ ∞ (allBranchExteriorNearChartWeight N θ η α δ h b ρ hδ q) :=
  (allBranchChartWeight_smooth N θ η α δ h hδ).mul
    ((microExteriorAnchor_smooth b q).mul (branch_shape_cutoffs_smooth ρ).2)

theorem allBranchExterior_near_chart_cutoff_jets (θ η α δ h : ℝ) (hδ : 0 < δ)
    (hθ : 0 < θ) (hθπ : θ < Real.pi) (hα : 0 < α) (hh : 0 < h)
    (hhθ : h ≤ θ/2) (hhπ : h ≤ (Real.pi-θ)/2) (J : ℕ) :
    ∃ C₀ C₁ K : ℝ, 1 ≤ C₀ ∧ 1 ≤ C₁ ∧ 1 ≤ K ∧ ∀ (N : ℕ) (b ρ : ℝ),
      0 < b → b ≤ 1 → 0 < ρ → ρ ≤ 1 → ∀ (q : Fin N) (u : Fin N → ℝ),
      0 < allBranchExteriorDiameter u → allBranchExteriorDiameter u ≤ 4*ρ →
      ∀ l : List (Fin N), l.length ≤ J →
      ‖cutoffJet l (allBranchExteriorNearChartWeight N θ η α δ h b ρ hδ q) u‖ ≤
        allBranchExteriorNearChartJetCost J N C₀ C₁ K b/allBranchExteriorDiameter u^l.length := by
  obtain ⟨C₀,hC₀,hchart⟩ := allBranchChartWeight_jet_bound θ η α δ h hδ hθ hθπ hα hh hhθ hhπ J
  obtain ⟨C₁,K,hC₁,hK,hexterior⟩ := microExteriorNearFar_sharp_jet_bound J
  refine ⟨C₀,C₁,K,hC₀,hC₁,hK,?_⟩
  intro N b ρ hb hb1 hρ hρ1 q u hdiam hdiamρ l hl
  have hgj (k : List (Fin N)) (hk : k.length ≤ J) :
      ‖cutoffJet k (microExteriorNearWeight b ρ q) u‖ ≤
        ((2:ℝ)^J*(C₁^N*(b⁻¹)^J)*(K*(1+24*N)^J))*(ρ⁻¹)^k.length := by
    have hh := (hexterior N b ρ hb hb1 hρ hρ1 q u k hk).1
    simpa only [mul_assoc] using hh
  exact cutoffJet_product_diameter_bound (allBranchChartWeight N θ η α δ h hδ)
    (microExteriorNearWeight b ρ q) (allBranchChartWeight_smooth N θ η α δ h hδ)
    ((microExteriorAnchor_smooth b q).mul (branch_shape_cutoffs_smooth ρ).2) u
    (by positivity) (by positivity) hρ hρ1 hdiam hdiamρ (by norm_num)
    (fun k hk => hchart N k hk u) hgj l hl

end
end IsingBulk.Tail
