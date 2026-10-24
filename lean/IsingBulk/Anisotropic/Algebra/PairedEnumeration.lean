import IsingBulk.Anisotropic.Algebra.EvenSchurDeterminant
import Mathlib.Data.List.OfFn

namespace IsingBulk.Anisotropic.Algebra
noncomputable section
open scoped BigOperators

def pairedIndices : (n : ℕ) → List (PairIndex n)
  | 0 => []
  | n+1 => .inl 0 :: .inl 1 :: (pairedIndices n).map Sum.inr

theorem pairedList_eq_map {n : ℕ} (v : PairIndex n → ℂ) :
    pairedList v = (pairedIndices n).map v := by
  induction n with
  | zero => rfl
  | succ n ih => simp [pairedList,pairedIndices,ih,List.map_map,Function.comp_def]

theorem mem_pairedIndices {n : ℕ} (i : PairIndex n) : i ∈ pairedIndices n := by
  induction n with
  | zero => exact i.elim
  | succ n ih =>
    rcases i with i | i
    · fin_cases i <;> simp [pairedIndices]
    · simp [pairedIndices,ih i]

theorem nodup_pairedIndices (n : ℕ) : (pairedIndices n).Nodup := by
  induction n with
  | zero => simp [pairedIndices]
  | succ n ih => simp [pairedIndices,List.nodup_map_iff Sum.inr_injective,ih]

theorem pairedIndices_perm_ofFn {n m : ℕ} (e : Fin m ≃ PairIndex n) :
    (pairedIndices n).Perm (List.ofFn e) := by
  apply (List.perm_ext_iff_of_nodup (nodup_pairedIndices n) (List.nodup_ofFn.mpr e.injective)).mpr
  intro i
  simp only [mem_pairedIndices, List.mem_ofFn]
  exact iff_of_true trivial (e.surjective i)

theorem norm_pairProduct_perm {xs ys : List ℂ} (hp : xs.Perm ys) :
    ‖IsingBulk.Schur.pairProduct schurKernel xs‖ =
    ‖IsingBulk.Schur.pairProduct schurKernel ys‖ := by
  induction hp with
  | nil => rfl
  | cons a hp ih =>
    simp only [IsingBulk.Schur.pairProduct,norm_mul]
    rw [(hp.map (schurKernel a)).prod_eq,ih]
  | swap a b xs =>
    simp only [IsingBulk.Schur.pairProduct,List.map_cons,List.prod_cons,norm_mul]
    have h : ‖schurKernel b a‖ = ‖schurKernel a b‖ := by rw [schurKernel_swap,norm_neg]
    rw [h]
    ring
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem norm_pairedList_eq_ofFn {n m : ℕ} (e : Fin m ≃ PairIndex n) (v : PairIndex n → ℂ) :
    ‖IsingBulk.Schur.pairProduct schurKernel (pairedList v)‖ =
      ‖IsingBulk.Schur.pairProduct schurKernel (List.ofFn (fun i => v (e i)))‖ := by
  rw [pairedList_eq_map]
  apply norm_pairProduct_perm
  simpa only [List.map_ofFn,Function.comp_def] using (pairedIndices_perm_ofFn e).map v

theorem card_pairIndex (n : ℕ) : Fintype.card (PairIndex n) = 2*n := by
  induction n with
  | zero => simp [PairIndex]
  | succ n ih =>
    change Fintype.card (Fin 2 ⊕ PairIndex n) = _
    rw [Fintype.card_sum,Fintype.card_fin,ih]
    omega

end
end IsingBulk.Anisotropic.Algebra
