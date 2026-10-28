import IsingBulk.HT22.Algebra.BorderedMinorBound

/-! # Genuine ordinary-only determinant jets and polynomial-degree vanishing -/
namespace IsingBulk.HT22.Algebra
noncomputable section
open IsingBulk.Preferred22
open scoped BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

/-- The variation of a constant-border matrix has zero ghost row and column. -/
def ordinaryDirection {N : ℕ} (B : Matrix (Fin N) (Fin N) ℂ) :
    Matrix (Fin (N+1)) (Fin (N+1)) ℂ := ghostBorder B (fun _ => 0)

/-- Only N² ordinary matrix units occur in a genuine bordered variation. -/
theorem ordinaryDirection_entry_expansion {N : ℕ} (B : Matrix (Fin N) (Fin N) ℂ) :
    ordinaryDirection B = ∑ a : Fin N × Fin N,
      B a.1 a.2 • Matrix.single a.1.succ a.2.succ (1:ℂ) := by
  classical
  ext i j
  cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp [ordinaryDirection, Matrix.single, Fintype.sum_prod_type,
      Matrix.sum_apply]
  simp [ite_and]

/-- Multilinearity restricts the exact jet expansion to ordinary marks. -/
theorem multilinear_ordinary_entry_expansion {N ell : ℕ}
    (F : (Matrix (Fin (N+1)) (Fin (N+1)) ℂ) [×ell]→L[ℂ] ℂ)
    (B : Fin ell → Matrix (Fin N) (Fin N) ℂ) :
    F (fun r => ordinaryDirection (B r)) =
      ∑ marks : Fin ell → Fin N × Fin N, (∏ r, B r (marks r).1 (marks r).2) *
        F (fun r => Matrix.single (marks r).1.succ (marks r).2.succ (1:ℂ)) := by
  classical
  have he : (fun r => ordinaryDirection (B r)) = fun r =>
      ∑ a : Fin N × Fin N, B r a.1 a.2 • Matrix.single a.1.succ a.2.succ (1:ℂ) := by
    funext r
    exact ordinaryDirection_entry_expansion (B r)
  rw [he]
  change F.toMultilinearMap (fun r => ∑ a : Fin N × Fin N,
    B r a.1 a.2 • Matrix.single a.1.succ a.2.succ (1:ℂ)) = _
  rw [F.toMultilinearMap.map_sum]
  apply Finset.sum_congr rfl
  intro marks _
  convert F.toMultilinearMap.map_smul_univ
    (fun r => B r (marks r).1 (marks r).2)
    (fun r => Matrix.single (marks r).1.succ (marks r).2.succ (1:ℂ)) using 1

/-- The true determinant derivative, with all ghost derivative terms removed
by their actual zero directions rather than by a hypothesis. -/
theorem bordered_determinant_jet_expansion {N ell : ℕ}
    (K : Matrix (Fin N) (Fin N) ℂ) (B : Fin ell → Matrix (Fin N) (Fin N) ℂ) :
    iteratedFDeriv ℂ ell Matrix.det (ghostBorder K (fun _ => 1))
      (fun r => ordinaryDirection (B r)) =
      ∑ marks : Fin ell → Fin N × Fin N,
        (∏ r, B r (marks r).1 (marks r).2) * borderedMarkedDeterminant K marks := by
  exact multilinear_ordinary_entry_expansion _ B

/-- There are exactly N^(2 ell) ordinary marking choices, not (N+1)^(2 ell). -/
theorem ordinary_marking_card (N ell : ℕ) :
    Fintype.card (Fin ell → Fin N × Fin N) = N^(2*ell) :=
  marked_entry_index_card N ell

/-- At least N ordinary entry marks annihilate the bordered determinant,
whose actual ordinary-entry polynomial degree is only N−1. -/
theorem borderedMarkedDeterminant_eq_zero_of_order {N ell : ℕ}
    (horder : N ≤ ell) (K : Matrix (Fin N) (Fin N) ℂ)
    (marks : Fin ell → Fin N × Fin N) : borderedMarkedDeterminant K marks = 0 := by
  classical
  by_cases hrow : Function.Injective (fun r => (marks r).1)
  · have hle : ell ≤ N := by
      simpa using Fintype.card_le_of_injective (fun r => (marks r).1) hrow
    have heq : ell = N := by omega
    subst ell
    have hs : Function.Surjective (fun r => (marks r).1) := Finite.surjective_of_injective hrow
    have hrow' : Function.Injective (fun r => (ordinaryMarks marks r).1) := by
      intro r t h
      exact hrow (Fin.succ_injective _ h)
    unfold borderedMarkedDeterminant
    rw [markedDeterminant_eq_row_replacement _ _ hrow']
    apply Matrix.det_eq_zero_of_column_eq_zero 0
    intro i
    cases i using Fin.cases with
    | zero =>
      have hzero : (0 : Fin (N+1)) ∉ Set.range (markedRowEmbedding (ordinaryMarks marks) hrow') := by
        rintro ⟨r,hr⟩
        exact Fin.succ_ne_zero (marks r).1 hr
      simp [replacedRows, hzero]
    | succ i =>
      obtain ⟨r, rfl⟩ := hs i
      have he := congrFun (marked_replacedRows_selected
        (ghostBorder K (fun _ => 1)) (ordinaryMarks marks) hrow' r) 0
      simpa [ordinaryMarks, Fin.succ_ne_zero] using he
  · simp only [Function.Injective] at hrow
    push Not at hrow
    obtain ⟨r,t,hrt,hne⟩ := hrow
    exact borderedMarkedDeterminant_row_collision K marks r t hne hrt

end
end IsingBulk.HT22.Algebra
