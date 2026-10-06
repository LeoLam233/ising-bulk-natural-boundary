import IsingBulk.Tail.AnchoredCutoffJets
import IsingBulk.Tail.ShapeCutoffJets
import IsingBulk.Tail.CoordinateProductJets

/-! Actual near/far named-cutoff jet costs with dimension and scale
quantifiers kept outside the particle and radial variables. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets Set
open scoped ContDiff BigOperators

theorem real_list_norm_sum_bound {I : Type*} (L : List I) (F : I → ℝ) (B : ℝ)
    (h : ∀ i ∈ L, ‖F i‖ ≤ B) : ‖(L.map F).sum‖ ≤ L.length*B := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ha := h a (by simp)
    have ht := ih (fun i hi => h i (by simp [hi]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    calc
      _ ≤ ‖F a‖+‖(L.map F).sum‖ := norm_add_le _ _
      _ ≤ B+L.length*B := add_le_add ha ht
      _ = _ := by ring

theorem cutoffJet_product_uniform_bound {N J : ℕ} (f g : (Fin N → ℝ) → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (u : Fin N → ℝ) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfb : ∀ l : List (Fin N), l.length ≤ J → ‖cutoffJet l f u‖ ≤ A)
    (hgb : ∀ l : List (Fin N), l.length ≤ J → ‖cutoffJet l g u‖ ≤ B)
    (l : List (Fin N)) (hl : l.length ≤ J) :
    ‖cutoffJet l (fun x => f x*g x) u‖ ≤ (2:ℝ)^J*A*B := by
  rw [cutoffJet_product_word l f g isOpen_univ (fun x _ => hf.contDiffAt)
    (fun x _ => hg.contDiffAt) u (mem_univ u)]
  have hh := real_list_norm_sum_bound (cutoffWordSplits l)
    (fun p => cutoffJet p.1 f u*cutoffJet p.2 g u) (A*B) (by
      intro p hp
      have ho := cutoffWordSplits_orders l p hp
      rw [norm_mul]
      exact mul_le_mul (hfb p.1 (by omega)) (hgb p.2 (by omega)) (norm_nonneg _) hA)
  rw [cutoffWordSplits_length,Nat.cast_pow,Nat.cast_ofNat] at hh
  exact hh.trans (by
    have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hl
    nlinarith [mul_nonneg hA hB])

theorem microExteriorNearFar_jet_bound (J : ℕ) :
    ∃ C K : ℝ, 1 ≤ C ∧ 1 ≤ K ∧ ∀ (N : ℕ) (b R rho : ℝ),
      0 < b → b ≤ 1 → 0 ≤ R → 0 < rho → ∀ (q : Fin N) (u : Fin N → ℝ),
      (∀ i, |u i| ≤ R) → ∀ l : List (Fin N), l.length ≤ J →
      ‖cutoffJet l (microExteriorNearWeight b rho q) u‖ ≤
        (2:ℝ)^J*(C^N*(b⁻¹)^J)*(1+J.factorial*K*(branchShapeJetCost N R rho)^J) ∧
      ‖cutoffJet l (microExteriorFarWeight b rho q) u‖ ≤
        (2:ℝ)^J*(C^N*(b⁻¹)^J)*(1+J.factorial*K*(branchShapeJetCost N R rho)^J) := by
  obtain ⟨C,hC,hanchor⟩ := microExteriorAnchor_jet_bound J
  obtain ⟨K,hK,hshape⟩ := branch_shape_cutoff_jet_bounds J
  refine ⟨C,K,hC,hK,?_⟩
  intro N b R rho hb hb1 hR hr q u hu l hl
  have hsh := hshape N R rho hR hr u hu
  have hB : 0 ≤ 1+J.factorial*K*(branchShapeJetCost N R rho)^J := by
    have hcost : 0 ≤ branchShapeJetCost N R rho := by unfold branchShapeJetCost; positivity
    positivity
  have hnear := cutoffJet_product_uniform_bound (microExteriorAnchor b q) (branchNearCutoff rho)
    (microExteriorAnchor_smooth b q) (branch_shape_cutoffs_smooth rho).2 u
    (show 0 ≤ C^N*(b⁻¹)^J by positivity) hB (fun l hl => hanchor N b hb hb1 q l hl u)
    (fun l hl => (hsh l hl).2) l hl
  have hfar := cutoffJet_product_uniform_bound (microExteriorAnchor b q) (branchFarCutoff rho)
    (microExteriorAnchor_smooth b q) (branch_shape_cutoffs_smooth rho).1 u
    (show 0 ≤ C^N*(b⁻¹)^J by positivity) hB (fun l hl => hanchor N b hb hb1 q l hl u)
    (fun l hl => (hsh l hl).1.trans (by linarith)) l hl
  exact ⟨hnear,hfar⟩

end
end IsingBulk.Tail
