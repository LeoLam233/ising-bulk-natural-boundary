import IsingBulk.Tail.IndexedPairSuppression
import IsingBulk.Tail.SelectorDefinitions

/-! Literal complete canceled-pair product: no ratio of products and no
assumption on assignment population. Scalar source attachments follow separately. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First
open scoped BigOperators

theorem canceledPairProduct_indexed_norm {N : ℕ} (z y : Fin N → ℂ) :
    ‖canceledPairProduct z y‖ = ∏ p ∈ orderedIndexPairs (Finset.univ : Finset (Fin N)),
      ‖canceledPair (y p.1) (y p.2) (z p.1) (z p.2)‖ := by
  simp only [canceledPairProduct,norm_prod,orderedIndexPairs,Finset.prod_filter,Finset.prod_product,apply_ite,norm_one]

theorem complete_pair_three_group_bound {N : ℕ} (z y : Fin N → ℂ)
    (g : Fin N → Fin 3) {q η : ℝ} (hq : 0 < q) (hq1 : q < 1) (hη : 0 ≤ η)
    (hslack : Real.log (1+η) ≤ -Real.log q/4)
    (hsame : ∀ i j, g i=g j → ‖canceledPair (y i) (y j) (z i) (z j)‖ ≤ q)
    (hcross : ∀ i j, g i≠g j → ‖canceledPair (y i) (y j) (z i) (z j)‖ ≤ 1+η) :
    ‖canceledPairProduct z y‖ ≤ (Real.exp (-Real.log q/2))^N*
      Real.exp (-(-Real.log q/12)*(N:ℝ)^2) := by
  rw [canceledPairProduct_indexed_norm]
  have hh := indexed_three_group_suppression (Finset.univ : Finset (Fin N)) g ∅ 0 (by simp)
    (fun p => canceledPair (y p.1) (y p.2) (z p.1) (z p.2)) q η hq hq1 hη hslack (by
      intro p _
      split_ifs with hc
      · exact hsame p.1 p.2 hc
      · exact hcross p.1 p.2 hc)
  simp only [Finset.sdiff_empty,Finset.card_univ,Fintype.card_fin,Nat.cast_zero,sub_zero] at hh
  apply hh.trans_eq
  rw [← Real.exp_nat_mul,← Real.exp_add]
  congr 1
  ring

/-- Deleted-factor version for direct Leibniz expansions, valid even when
an omitted complete-pair factor vanishes. -/
theorem complete_pair_deleted_three_group_bound {N : ℕ} (z y : Fin N → ℂ)
    (g : Fin N → Fin 3) (E : Finset (Fin N × Fin N)) (j : ℕ) (hE : E.card ≤ j)
    {q η : ℝ} (hq : 0 < q) (hq1 : q < 1) (hη : 0 ≤ η)
    (hslack : Real.log (1+η) ≤ -Real.log q/4)
    (hsame : ∀ i k, g i=g k → ‖canceledPair (y i) (y k) (z i) (z k)‖ ≤ q)
    (hcross : ∀ i k, g i≠g k → ‖canceledPair (y i) (y k) (z i) (z k)‖ ≤ 1+η) :
    (∏ p ∈ orderedIndexPairs (Finset.univ : Finset (Fin N)) \ E,
      ‖canceledPair (y p.1) (y p.2) (z p.1) (z p.2)‖) ≤
      Real.exp (-j*Real.log q)*(Real.exp (-Real.log q/2))^N*
        Real.exp (-(-Real.log q/12)*(N:ℝ)^2) := by
  have hh := indexed_three_group_suppression (Finset.univ : Finset (Fin N)) g E j hE
    (fun p => canceledPair (y p.1) (y p.2) (z p.1) (z p.2)) q η hq hq1 hη hslack (by
      intro p _
      split_ifs with hc
      · exact hsame p.1 p.2 hc
      · exact hcross p.1 p.2 hc)
  simp only [Finset.card_univ,Fintype.card_fin] at hh
  apply hh.trans_eq
  rw [← Real.exp_nat_mul,← Real.exp_add,← Real.exp_add]
  congr 1
  ring

end
end IsingBulk.Tail
