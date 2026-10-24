import IsingBulk.Anisotropic.RegularEdges.RootGap

noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace IsingBulk.Anisotropic.RegularEdges

def edgeRootProduct {N : ℕ} (b : ℝ) (B : ℂ → ℂ) (u : ℂ) (q : Fin N → ℝ) : ℂ :=
  ∏ i, edgeParamRoot b B u (q i)

 theorem root_product_norm_le_factor {N : ℕ} (z : Fin N → ℂ)
    (hz : ∀ i, ‖z i‖≤1) (i : Fin N) : ‖∏ a,z a‖≤‖z i‖ := by
  rw [norm_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  apply mul_le_of_le_one_right (norm_nonneg _)
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun a _ => hz a)

/-- A single maximal retained coordinate controls the full product denominator.
There is no lost factor of the total particle number. -/
theorem root_product_retained_gap {N m : ℕ} [Nonempty (Fin m)]
    (z : Fin N → ℂ) (q : Fin N → ℝ) (p : Fin m → Fin N) {c ε : ℝ}
    (hc : 0<c) (hε : 0<ε)
    (hg : ∀ i, c*(ε+(q i)^2)≤1-‖z i‖) :
    0<c*(ε+‖fun i => q (p i)‖^2) ∧
    c*(ε+‖fun i => q (p i)‖^2)≤1 ∧
    c*(ε+‖fun i => q (p i)‖^2)≤‖1-∏ i,z i‖ := by
  have hz (i : Fin N) : ‖z i‖≤1 := by
    have h := hg i
    have hp : 0<c*(ε+(q i)^2) := by positivity
    linarith
  obtain ⟨i,hi⟩ := (IsGreatest.pi_norm (fun i => q (p i))).1
  have he : ‖fun i => q (p i)‖^2=(q (p i))^2 := by
    rw [←hi]
    change ‖q (p i)‖^2=(q (p i))^2
    rw [Real.norm_eq_abs, sq_abs]
  have hg' := hg (p i)
  rw [←he] at hg'
  refine ⟨by positivity,?_,?_⟩
  · exact hg'.trans (sub_le_self _ (norm_nonneg _))
  · have hp := root_product_norm_le_factor z hz (p i)
    have hn := norm_sub_norm_le (1:ℂ) (∏ i,z i)
    rw [norm_one] at hn
    linarith

 theorem edgeRootProduct_retained_gap {b : ℝ} {B : ℂ → ℂ}
    (hB : 0<(B 0).im) (hc : ContinuousAt B 0) :
    ∃ c δ : ℝ, 0<c ∧ 0<δ ∧ ∀ ε : ℝ, 0<ε → ε<δ →
      ∀ (N m : ℕ) [Nonempty (Fin m)] (q : Fin N → ℝ) (p : Fin m → Fin N),
      (∀ i, q i∈Icc (-Real.pi) Real.pi) →
      0<c*(ε+‖fun i => q (p i)‖^2) ∧
      c*(ε+‖fun i => q (p i)‖^2)≤1 ∧
      c*(ε+‖fun i => q (p i)‖^2)≤‖1-edgeRootProduct b B (Complex.I*(ε:ℂ)) q‖ := by
  obtain ⟨c,δ,hcpos,hδ,hg⟩ := edgeParamRoot_inward_gap (b := b) hB hc
  refine ⟨c,δ,hcpos,hδ,?_⟩
  intro ε hε hεδ N m _ q p hq
  exact root_product_retained_gap _ q p hcpos hε (fun i => hg ε hε hεδ (q i) (hq i))

end IsingBulk.Anisotropic.RegularEdges
