import IsingBulk.Preferred22.MarkedDeterminant
import Mathlib.Topology.Algebra.Group.Matrix

/-! The marked determinant derivatives are genuine signed complementary
minors: a repeated marked row gives zero, and distinct marked rows select
the actual determinant with those rows replaced by coordinate rows. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

def rowDeterminant (N : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin N => Fin N → ℂ) ℂ where
  toMultilinearMap := Matrix.detRowAlternating.toMultilinearMap
  cont := continuous_id.matrix_det

@[simp] theorem rowDeterminant_apply (N : ℕ) (K : Matrix (Fin N) (Fin N) ℂ) :
    rowDeterminant N K = K.det := rfl

def replacedRows {N ell : ℕ} (K : Matrix (Fin N) (Fin N) ℂ)
    (B : Fin ell → Matrix (Fin N) (Fin N) ℂ) (e : Fin ell ↪ Fin N) :
    Matrix (Fin N) (Fin N) ℂ :=
  fun i => if hi : i ∈ Set.range e then B (e.toEquivRange.symm ⟨i,hi⟩) i else K i

theorem determinant_jet_row_expansion {N ell : ℕ}
    (K : Matrix (Fin N) (Fin N) ℂ)
    (B : Fin ell → Matrix (Fin N) (Fin N) ℂ) :
    iteratedFDeriv ℂ ell Matrix.det K B =
      ∑ e : Fin ell ↪ Fin N, (replacedRows K B e).det := by
  classical
  change iteratedFDeriv ℂ ell (rowDeterminant N) K B = _
  rw [(rowDeterminant N).iteratedFDeriv_eq]
  simp only [ContinuousMultilinearMap.iteratedFDeriv, sum_apply,
    ContinuousMultilinearMap.iteratedFDerivComponent_apply, Pi.compRightL_apply,
    rowDeterminant_apply]
  apply Finset.sum_congr rfl
  intro e _
  unfold replacedRows
  congr 1
  funext i
  by_cases hi : i ∈ Set.range e
  · obtain ⟨r,rfl⟩ := hi
    simp [Function.Embedding.toEquivRange_symm_apply_self]
  · simp [hi]

theorem replacedRows_apply_embedding {N ell : ℕ}
    (K : Matrix (Fin N) (Fin N) ℂ)
    (B : Fin ell → Matrix (Fin N) (Fin N) ℂ)
    (e : Fin ell ↪ Fin N) (r : Fin ell) :
    replacedRows K B e (e r) = B r (e r) := by
  simp [replacedRows, Function.Embedding.toEquivRange_symm_apply_self]

theorem marked_replacedRows_det_zero {N ell : ℕ}
    (K : Matrix (Fin N) (Fin N) ℂ) (marks : Fin ell → Fin N × Fin N)
    (e : Fin ell ↪ Fin N) (r : Fin ell) (hr : e r ≠ (marks r).1) :
    (replacedRows K (fun k => Matrix.single (marks k).1 (marks k).2 (1:ℂ)) e).det = 0 := by
  apply Matrix.det_eq_zero_of_row_eq_zero (e r)
  intro j
  rw [replacedRows_apply_embedding]
  simp [Matrix.single, Ne.symm hr]

/-- Repeated row marks vanish identically, including at singular matrices. -/
theorem markedDeterminant_eq_zero_of_row_collision {N ell : ℕ}
    (K : Matrix (Fin N) (Fin N) ℂ) (marks : Fin ell → Fin N × Fin N)
    (r t : Fin ell) (hrt : r ≠ t) (hrow : (marks r).1 = (marks t).1) :
    markedDeterminant K marks = 0 := by
  classical
  rw [markedDeterminant, determinant_jet_row_expansion]
  apply Finset.sum_eq_zero
  intro e _
  have hmis : ∃ k, e k ≠ (marks k).1 := by
    by_contra hn
    push Not at hn
    exact hrt (e.injective ((hn r).trans (hrow.trans (hn t).symm)))
  obtain ⟨k,hk⟩ := hmis
  exact marked_replacedRows_det_zero K marks e k hk

def markedRowEmbedding {N ell : ℕ} (marks : Fin ell → Fin N × Fin N)
    (hrow : Function.Injective (fun r => (marks r).1)) : Fin ell ↪ Fin N :=
  ⟨fun r => (marks r).1, hrow⟩

/-- Exact signed complementary determinant, expressed without choosing an
ordering of the remaining rows and columns. -/
theorem markedDeterminant_eq_row_replacement {N ell : ℕ}
    (K : Matrix (Fin N) (Fin N) ℂ) (marks : Fin ell → Fin N × Fin N)
    (hrow : Function.Injective (fun r => (marks r).1)) :
    markedDeterminant K marks =
      (replacedRows K (fun r => Matrix.single (marks r).1 (marks r).2 (1:ℂ))
        (markedRowEmbedding marks hrow)).det := by
  classical
  rw [markedDeterminant, determinant_jet_row_expansion]
  apply Finset.sum_eq_single (markedRowEmbedding marks hrow)
  · intro e _ he
    have hmis : ∃ r, e r ≠ (marks r).1 := by
      by_contra hn
      push Not at hn
      apply he
      ext r
      exact congrArg Fin.val (hn r)
    obtain ⟨r,hr⟩ := hmis
    exact marked_replacedRows_det_zero K marks e r hr
  · simp

theorem marked_replacedRows_selected {N ell : ℕ}
    (K : Matrix (Fin N) (Fin N) ℂ) (marks : Fin ell → Fin N × Fin N)
    (hrow : Function.Injective (fun r => (marks r).1)) (r : Fin ell) :
    replacedRows K (fun k => Matrix.single (marks k).1 (marks k).2 (1:ℂ))
      (markedRowEmbedding marks hrow) (marks r).1 = Pi.single (marks r).2 1 := by
  change replacedRows K (fun k => Matrix.single (marks k).1 (marks k).2 (1:ℂ))
    (markedRowEmbedding marks hrow) ((markedRowEmbedding marks hrow) r) = _
  rw [replacedRows_apply_embedding]
  ext j
  simp [markedRowEmbedding, Matrix.single, Pi.single_apply, eq_comm]

/-- Repeated column marks also vanish; no nonsingularity assumption is used. -/
theorem markedDeterminant_eq_zero_of_column_collision {N ell : ℕ}
    (K : Matrix (Fin N) (Fin N) ℂ) (marks : Fin ell → Fin N × Fin N)
    (r t : Fin ell) (hrt : r ≠ t) (hcol : (marks r).2 = (marks t).2) :
    markedDeterminant K marks = 0 := by
  classical
  by_cases hrow : Function.Injective (fun k => (marks k).1)
  · rw [markedDeterminant_eq_row_replacement K marks hrow]
    apply Matrix.det_zero_of_row_eq (fun he => hrt (hrow he))
    rw [marked_replacedRows_selected, marked_replacedRows_selected, hcol]
  · simp only [Function.Injective] at hrow
    push Not at hrow
    obtain ⟨a,b,hab,hne⟩ := hrow
    exact markedDeterminant_eq_zero_of_row_collision K marks a b hne hab

end
end IsingBulk.Preferred22
