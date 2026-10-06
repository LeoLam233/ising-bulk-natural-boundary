import IsingBulk.Tail.IndexedPairCounting
import IsingBulk.Tail.PairCounting

/-! Direct surviving-product suppression for actual indexed pairs. Both
same and cross cardinalities are proved, never caller-supplied certificates. -/
namespace IsingBulk.Tail
noncomputable section
open scoped BigOperators

 theorem indexed_remaining_same_lower {α : Type*} [LinearOrder α]
    (s : Finset α) (g : α → Fin 3) (E : Finset (α × α)) (j : ℕ) (hE : E.card ≤ j) :
    (s.card:ℝ)^2/6-(s.card:ℝ)/2-j ≤
      ((((orderedIndexPairs s) \ E).filter (fun p => g p.1=g p.2)).card:ℝ) := by
  have he : ((orderedIndexPairs s) \ E).filter (fun p => g p.1=g p.2)=sameColorPairs s g \ E := by
    ext p
    simp [sameColorPairs,and_left_comm,and_comm]
  rw [he]
  have hcount := threeColorPairs_lower s g
  have hremove := remaining_card_lower (sameColorPairs s g) E j hE
  linarith

 theorem indexed_remaining_cross_upper {α : Type*} [LinearOrder α]
    (s : Finset α) (g : α → Fin 3) (E : Finset (α × α)) :
    ((((orderedIndexPairs s) \ E).filter (fun p => g p.1≠g p.2)).card:ℝ) ≤ (s.card:ℝ)^2/3 := by
  have hsub : ((orderedIndexPairs s) \ E).filter (fun p => g p.1≠g p.2) ⊆
      (orderedIndexPairs s).filter (fun p => g p.1≠g p.2) := by
    intro p hp
    simp only [Finset.mem_filter,Finset.mem_sdiff] at hp ⊢
    exact ⟨hp.1.1,hp.2⟩
  have hc : ((((orderedIndexPairs s) \ E).filter (fun p => g p.1≠g p.2)).card:ℝ) ≤
      (((orderedIndexPairs s).filter (fun p => g p.1≠g p.2)).card:ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  exact hc.trans (threeColorPairs_cross_upper s g)

/-- Every deleted factor may vanish. Bounds are applied directly to the
remaining indexed factors, with the same constants for every assignment. -/
 theorem indexed_three_group_suppression {α : Type*} [LinearOrder α]
    (s : Finset α) (g : α → Fin 3) (E : Finset (α × α)) (j : ℕ) (hE : E.card ≤ j)
    (P : α × α → ℂ) (q η : ℝ) (hq : 0 < q) (hq1 : q < 1) (hη : 0 ≤ η)
    (hslack : Real.log (1+η) ≤ -Real.log q/4)
    (hp : ∀ p ∈ orderedIndexPairs s \ E,
      ‖P p‖ ≤ if g p.1=g p.2 then q else 1+η) :
    (∏ p ∈ orderedIndexPairs s \ E, ‖P p‖) ≤
      Real.exp (((s.card:ℝ)^2/12-(s.card:ℝ)/2-j)*Real.log q) := by
  have hlogq : Real.log q < 0 := Real.log_neg hq hq1
  have hlogη : 0 ≤ Real.log (1+η) := Real.log_nonneg (by linarith)
  apply surviving_pair_suppression (orderedIndexPairs s \ E) (fun p => g p.1=g p.2)
    (fun p => ‖P p‖) (s.card:ℝ) j (Real.log q) (Real.log (1+η)) hlogq hlogη hslack
    (indexed_remaining_same_lower s g E j hE) (indexed_remaining_cross_upper s g E)
    (fun _ _ => norm_nonneg _)
  intro p hp'
  have hh := hp p hp'
  split_ifs with hc
  · simpa [hc,Real.exp_log hq] using hh
  · simpa [hc,Real.exp_log (show 0 < 1+η by linarith)] using hh

end
end IsingBulk.Tail
