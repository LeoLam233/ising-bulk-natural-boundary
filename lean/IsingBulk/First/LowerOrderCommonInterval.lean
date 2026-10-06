import IsingBulk.First.LowerOrderFixedRadius

/-! The approved published fixed-order input yields a common positive radial
interval for any finite set of lower particle and derivative orders. No
common interval over infinitely many derivative orders is asserted. -/
namespace IsingBulk.First
noncomputable section

private theorem finite_positive_common_radius {ι : Type*} (S : Finset ι) (r : ι → ℝ)
    (hr : ∀ i ∈ S, 0 < r i) : ∃ e : ℝ, 0 < e ∧ ∀ i ∈ S, e ≤ r i := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,by simp⟩
  | @insert i S hi ih =>
    obtain ⟨e,he,hb⟩ := ih (fun j hj => hr j (Finset.mem_insert_of_mem hj))
    refine ⟨min (r i) e,lt_min (hr i (Finset.mem_insert_self _ _)) he,?_⟩
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hb j hj)

theorem selected_lower_orders_common_interval {p : ℕ} {a b : ℤ}
    (hp : p.Prime) (hp11 : 11 ≤ p)
    (ha : PrimeFamily.Admissible p a) (hb : PrimeFamily.Admissible p b)
    (hTW : PublishedTWFixedOrderInput (PrimeFamily.selectedPoint p a b)) (m : ℕ) :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ ∀ N : ℕ, 0 < N → Even N → N < 2*p →
      ∀ j : ℕ, j ≤ m → ∃ C : ℝ, 0 ≤ C ∧ ∀ epsilon : ℝ,
        0 < epsilon → epsilon < epsilon₀ →
        ‖(deriv^[j] (doubleFormFactor N (sourceRadialPair (selectedOrderedChart ha hb).theta epsilon).1))
          (sourceRadialPair (selectedOrderedChart ha hb).theta epsilon).2‖ ≤ C := by
  classical
  let I := {N : Fin (2*p) // 0 < N.val ∧ Even N.val} × Fin (m+1)
  have hfixed (i : I) := selected_lower_orders_fixed_radius_bounded hp hp11 ha hb hTW
    i.1.1 i.1.2.1 i.1.2.2 i.1.1.2 i.2
  choose radius bound hr hC hB using hfixed
  obtain ⟨epsilon₀,he0,hmin⟩ := finite_positive_common_radius Finset.univ radius (fun i _ => hr i)
  refine ⟨epsilon₀,he0,?_⟩
  intro N hN he hNp j hj
  let i : I := (⟨⟨N,hNp⟩,hN,he⟩,⟨j,by omega⟩)
  refine ⟨bound i,hC i,?_⟩
  intro epsilon heps heps0
  exact hB i epsilon heps (heps0.trans_le (hmin i (Finset.mem_univ i)))

end
end IsingBulk.First
