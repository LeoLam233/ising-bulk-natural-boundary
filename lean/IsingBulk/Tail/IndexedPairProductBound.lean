import IsingBulk.Tail.IndexedPairCounting
import IsingBulk.Tail.PairCounting

/-! Source-indexed compact-group contraction, allowing every other pair its
own small 1+C/N inflation. No pair is divided out. -/
namespace IsingBulk.Tail
noncomputable section
open scoped BigOperators

theorem indexed_two_group_product_bound {N : ℕ} (hN : 0 < N)
    (J : Finset (Fin N)) (g : Fin N → Fin 2) (f : Fin N × Fin N → ℝ)
    {C q : ℝ} (hC : 0 ≤ C) (hq : 0 < q) (hq1 : q < 1)
    (hf : ∀ p ∈ orderedIndexPairs (Finset.univ : Finset (Fin N)), 0 ≤ f p)
    (hb : ∀ p ∈ orderedIndexPairs (Finset.univ : Finset (Fin N)), f p ≤ 1+C/N)
    (hs : ∀ p ∈ sameColorPairs J g, f p ≤ q) :
    (∏ p ∈ orderedIndexPairs (Finset.univ : Finset (Fin N)), f p) ≤
      Real.exp ((C-Real.log q/2)*N)*Real.exp ((Real.log q/4)*(J.card : ℝ)^2) := by
  let S := orderedIndexPairs (Finset.univ : Finset (Fin N))
  let A := sameColorPairs J g
  have hAS : A ⊆ S := by
    intro p hp
    simp only [A,S,sameColorPairs,orderedIndexPairs,Finset.mem_filter,
      Finset.mem_product,Finset.mem_univ,true_and] at hp ⊢
    exact hp.1.2
  have he : S.filter (fun p => p∈A) = A := by
    ext p
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hAS h,h⟩⟩
  have hNR : (0:ℝ)<N := by exact_mod_cast hN
  have hlog : Real.log q < 0 := Real.log_neg hq hq1
  have hprod := product_exp_bound S f
    (fun p => if p∈A then Real.log q else C/N) hf (by
      intro p hp
      by_cases ha : p∈A
      · simp only [ha,ite_true,Real.exp_log hq]
        exact hs p ha
      · simp only [ha,ite_false]
        exact (hb p hp).trans (by simpa [add_comm] using Real.add_one_le_exp (C/N)))
  rw [← Real.exp_add]
  apply hprod.trans
  apply Real.exp_le_exp.mpr
  rw [Finset.sum_ite,Finset.sum_const,Finset.sum_const,he]
  simp only [nsmul_eq_mul]
  have ha := twoColorPairs_lower J g
  change (J.card : ℝ)^2/4-(J.card : ℝ)/2 ≤ (A.card : ℝ) at ha
  have hM : (J.card : ℝ) ≤ N := by
    exact_mod_cast (show J.card ≤ N by simpa using Finset.card_le_univ J)
  have hcrossNat : (S.filter (fun p => p∉A)).card ≤ N*N := by
    apply (Finset.card_le_card (Finset.filter_subset _ _)).trans
    have ht : S ⊆ (Finset.univ : Finset (Fin N)) ×ˢ Finset.univ :=
      Finset.filter_subset _ _
    simpa only [Finset.card_product,Finset.card_univ,Fintype.card_fin] using
      Finset.card_le_card ht
  have hcross : ((S.filter (fun p => p∉A)).card : ℝ) ≤ (N:ℝ)^2 := by
    exact_mod_cast (show (S.filter (fun p => p∉A)).card ≤ N^2 by
      simpa only [pow_two] using hcrossNat)
  have hterm : ((S.filter (fun p => p∉A)).card : ℝ)*(C/N) ≤ C*N := by
    calc
      _ ≤ (N:ℝ)^2*(C/N) := mul_le_mul_of_nonneg_right hcross (div_nonneg hC hNR.le)
      _ = C*N := by field_simp
  have hsame := mul_le_mul_of_nonpos_right ha hlog.le
  have hlinear := mul_le_mul_of_nonneg_left hM (neg_nonneg.mpr hlog.le)
  nlinarith

end
end IsingBulk.Tail
