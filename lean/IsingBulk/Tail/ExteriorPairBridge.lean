import IsingBulk.First.ContourDefinitions
import IsingBulk.Algebra.SchurContinuation
import Mathlib.Algebra.BigOperators.Fin

/-! Identification of FIRST's complete indexed pair product with the frozen
Schur endpoint's list product. This bridge preserves all pairs and signs. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First
open scoped BigOperators

theorem pairProduct_eq_schur (N : ℕ) (x : Fin N → ℂ) :
    First.pairProduct x = Schur.pairProduct pairKernel (List.ofFn x) := by
  induction N with
  | zero => simp [First.pairProduct, Schur.pairProduct]
  | succ N ih =>
    rw [List.ofFn_succ, Schur.pairProduct, List.map_ofFn, List.prod_ofFn]
    rw [← ih (fun i => x i.succ)]
    simp only [First.pairProduct, Finset.prod_filter]
    rw [Fin.prod_univ_succ]
    simp [Fin.prod_univ_succ, Fin.succ_pos]

end
end IsingBulk.Tail
