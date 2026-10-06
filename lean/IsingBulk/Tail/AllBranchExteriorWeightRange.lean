import IsingBulk.Tail.AllBranchExteriorEqualityGeometry

namespace IsingBulk.Tail
noncomputable section
open Set

theorem allBranchExterior_pairWeight_le_one_ordered {N : ℕ} (M : ℕ) (p q : Fin N)
    (hpq : p < q) (u : Fin N → ℝ) : allBranchExteriorPairWeight M p q u ≤ 1 := by
  have hmem : (p,q) ∈ orderedIndexPairs (Finset.univ : Finset (Fin N)) := by simp [orderedIndexPairs,hpq]
  have hsum : (u p-u q)^(2*M) ≤ allBranchExteriorWeightDenom M u := by
    exact Finset.single_le_sum (fun r (_ : r ∈ orderedIndexPairs (Finset.univ : Finset (Fin N))) =>
      (show 0 ≤ (u r.1-u r.2)^(2*M) by rw [pow_mul]; positivity)) hmem
  by_cases hz : allBranchExteriorWeightDenom M u=0
  · simp [allBranchExteriorPairWeight,hz]
  · exact (div_le_one (lt_of_le_of_ne (allBranchExterior_weightDenom_nonneg M u) (Ne.symm hz))).mpr hsum

theorem allBranchExterior_pairWeight_symm {N : ℕ} (M : ℕ) (p q : Fin N) (u : Fin N → ℝ) :
    allBranchExteriorPairWeight M p q u=allBranchExteriorPairWeight M q p u := by
  unfold allBranchExteriorPairWeight
  congr 1
  rw [pow_mul,pow_mul]
  congr 1
  ring

theorem allBranchExterior_pairWeight_le_one {N : ℕ} (M : ℕ) (p q : Fin N)
    (hpq : p ≠ q) (u : Fin N → ℝ) : allBranchExteriorPairWeight M p q u ≤ 1 := by
  rcases lt_or_gt_of_ne hpq with h|h
  · exact allBranchExterior_pairWeight_le_one_ordered M p q h u
  · rw [allBranchExterior_pairWeight_symm]
    exact allBranchExterior_pairWeight_le_one_ordered M q p h u

theorem allBranchExterior_pairWeight_measurable {N : ℕ} (M : ℕ) (p q : Fin N) :
    Measurable (allBranchExteriorPairWeight M p q) := by
  unfold allBranchExteriorPairWeight allBranchExteriorWeightDenom
  fun_prop

end
end IsingBulk.Tail
