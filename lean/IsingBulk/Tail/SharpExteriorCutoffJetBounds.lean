import IsingBulk.Tail.ExteriorCutoffJetBounds
import IsingBulk.Tail.SharpShapeCutoffJets

/-! Near-collision cutoffs retain exactly one inverse rho per real word
letter. The anchored b loss is a separate harmless exponential-N cost. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets
open scoped ContDiff

theorem microExteriorNearFar_sharp_jet_bound (J : ℕ) :
    ∃ C K : ℝ, 1 ≤ C ∧ 1 ≤ K ∧ ∀ (N : ℕ) (b rho : ℝ),
      0 < b → b ≤ 1 → 0 < rho → rho ≤ 1 → ∀ (q : Fin N) (u : Fin N → ℝ),
      ∀ l : List (Fin N), l.length ≤ J →
      ‖cutoffJet l (microExteriorNearWeight b rho q) u‖ ≤
        (2:ℝ)^J*(C^N*(b⁻¹)^J)*(K*(1+24*N)^J*(rho⁻¹)^l.length) ∧
      ‖cutoffJet l (microExteriorFarWeight b rho q) u‖ ≤
        (2:ℝ)^J*(C^N*(b⁻¹)^J)*(K*(1+24*N)^J*(rho⁻¹)^l.length) := by
  obtain ⟨C,hC,hanchor⟩ := microExteriorAnchor_jet_bound J
  obtain ⟨K,hK,hshape⟩ := branch_shape_cutoff_sharp_words J
  refine ⟨C,K,hC,hK,?_⟩
  intro N b rho hb hb1 hr hr1 q u l hl
  have hcombined (g : (Fin N → ℝ) → ℝ) (hg : ContDiff ℝ ∞ g)
      (hgb : ∀ k : List (Fin N), k.length ≤ J →
        ‖cutoffJet k g u‖ ≤ K*(1+24*N)^J*(rho⁻¹)^k.length) :
      ‖cutoffJet l (fun x => microExteriorAnchor b q x*g x) u‖ ≤
        (2:ℝ)^J*(C^N*(b⁻¹)^J)*(K*(1+24*N)^J*(rho⁻¹)^l.length) := by
    have hh := cutoffJet_product_uniform_bound (J := l.length) (microExteriorAnchor b q) g
      (microExteriorAnchor_smooth b q) hg u
      (show 0 ≤ C^N*(b⁻¹)^J by positivity)
      (show 0 ≤ K*(1+24*(N:ℝ))^J*(rho⁻¹)^l.length by positivity)
      (fun k hk => hanchor N b hb hb1 q k (hk.trans hl) u)
      (fun k hk => (hgb k (hk.trans hl)).trans (by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_right₀ ((one_le_inv₀ hr).mpr hr1) hk)) l le_rfl
    exact hh.trans (by gcongr; norm_num)
  exact ⟨hcombined _ (branch_shape_cutoffs_smooth rho).2 (fun k hk => (hshape N rho hr u k hk).2),
    hcombined _ (branch_shape_cutoffs_smooth rho).1 (fun k hk => (hshape N rho hr u k hk).1)⟩

end
end IsingBulk.Tail
