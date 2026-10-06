import IsingBulk.First.LowerOrderFixedRadius

/-! The finitely many lower orders and finitely many derivatives share one
actual source approach interval and one bound. No infinite tail enters. -/
namespace IsingBulk.First
noncomputable section
open scoped BigOperators

private theorem positive_finite_common_threshold {ι : Type*} (I : Finset ι)
    (e : ι → ℝ) (he : ∀ i ∈ I, 0 < e i) :
    ∃ d : ℝ, 0 < d ∧ ∀ i ∈ I, d ≤ e i := by
  classical
  induction I using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | @insert i I hi ih =>
    obtain ⟨d,hd,hb⟩ := ih (fun a ha => he a (Finset.mem_insert_of_mem ha))
    refine ⟨min (e i) d,lt_min (he i (Finset.mem_insert_self _ _)) hd,?_⟩
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hb a ha)

theorem selected_lower_finite_window_bounded {p : ℕ} {a b : ℤ}
    (hp : p.Prime) (hp11 : 11 ≤ p)
    (ha : PrimeFamily.Admissible p a) (hb : PrimeFamily.Admissible p b)
    (hTW : PublishedTWFixedOrderInput (PrimeFamily.selectedPoint p a b)) (k : ℕ) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∀ N : ℕ, 0 < N → Even N → N < 2*p → ∀ j : ℕ, j ≤ k →
        ‖(deriv^[j] (doubleFormFactor N (sourceRadialPair (selectedOrderedChart ha hb).theta ε).1))
          (sourceRadialPair (selectedOrderedChart ha hb).theta ε).2‖ ≤ C := by
  classical
  let I := {n : Fin (2*p) // 0 < n.1 ∧ Even n.1} × Fin (k+1)
  have hlocal (i : I) := selected_lower_orders_fixed_radius_bounded hp hp11 ha hb hTW
    i.1.1.1 i.1.2.1 i.1.2.2 i.1.1.2 i.2.1
  choose e C he hC hbnd using hlocal
  obtain ⟨d,hd,hmin⟩ := positive_finite_common_threshold Finset.univ e (fun i _ => he i)
  refine ⟨d,∑ i, C i,hd,Finset.sum_nonneg (fun i _ => hC i),?_⟩
  intro ε hε hεd N hN heven hNp j hj
  let i : I := (⟨⟨N,hNp⟩,hN,heven⟩,⟨j,by omega⟩)
  exact (hbnd i ε hε (hεd.trans_le (hmin i (Finset.mem_univ i)))).trans
    (Finset.single_le_sum (fun q _ => hC q) (Finset.mem_univ i))

end
end IsingBulk.First
