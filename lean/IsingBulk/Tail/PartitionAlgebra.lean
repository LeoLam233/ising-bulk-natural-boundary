import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! Fixed support partition algebra for manuscript Lemma 7.1. Labels are
created before differentiation; their closed support survives every finite
jet. This file supplies the telescope and support logic, not the unresolved
geometric construction of periodic left/right labels. -/
namespace IsingBulk.Tail
noncomputable section
open scoped BigOperators
open Set Function

def outerAnchor (chi : ℕ → ℝ) (q : ℕ) : ℝ :=
  (1-chi q) * ∏ i ∈ Finset.range q, chi i

theorem outerAnchor_telescope (chi : ℕ → ℝ) (N : ℕ) :
    (∏ i ∈ Finset.range N, chi i) +
      ∑ q ∈ Finset.range N, outerAnchor chi q = 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ]
    unfold outerAnchor
    unfold outerAnchor at ih
    linear_combination ih

/-- A nonzero anchored term necessarily retains its named outer index. -/
theorem outerAnchor_ne_zero (chi : ℕ → ℝ) (q : ℕ)
    (h : outerAnchor chi q ≠ 0) : chi q ≠ 1 := by
  intro he
  simp [outerAnchor, he] at h

/-- Closure is essential: derivative support is contained in closed support,
not in the generally open nonzero locus. -/
theorem finite_jet_retains_closed_support {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : E → ℝ) (C : Set E) (hC : IsClosed C)
    (hw : support w ⊆ C) (j : ℕ) :
    tsupport (iteratedFDeriv ℝ j w) ⊆ C := by
  exact (tsupport_iteratedFDeriv_subset j).trans (closure_minimal hw hC)

/-- A current has a named nonbranch index, even if every other index is
true branch. There is therefore no all-branch current sector. -/
theorem named_current_not_all_branch {N : ℕ} (branch : Fin N → Prop)
    (q : Fin N) (hq : ¬ branch q) : ¬ ∀ i, branch i := by
  intro h
  exact hq (h q)

/-- The three non-all-branch alternatives are exhaustive. The compact
anchor is supplied by the telescope (or by the named current index). -/
theorem compact_branch_alternatives {N : ℕ}
    (left branch : Fin N → Prop) (q : Fin N) (hq : ¬ branch q) :
    (∃ i, left i) ∨
      ((¬ ∃ i, left i) ∧ ∃ j, branch j ∧ j ≠ q) ∨
      ((∀ i, ¬ left i) ∧ ∀ i, ¬ branch i) := by
  classical
  by_cases hl : ∃ i, left i
  · exact Or.inl hl
  · by_cases hb : ∃ j, branch j
    · obtain ⟨j,hj⟩ := hb
      exact Or.inr (Or.inl ⟨hl,j,hj,by rintro rfl; exact hq hj⟩)
    · exact Or.inr (Or.inr ⟨fun i hi => hl ⟨i,hi⟩,fun i hi => hb ⟨i,hi⟩⟩)

end
end IsingBulk.Tail
