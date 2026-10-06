import IsingBulk.Tail.PfaffianPairings
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.FinRange

/-! Every recursively enumerated matching supplies an actual bijection from
pair slots to source coordinates. No omitted or duplicated coordinate remains. -/
namespace IsingBulk.Tail
noncomputable section
open scoped BigOperators

variable {α : Type*}

theorem pairingLabels_length (M : List (α × α)) : (pairingLabels M).length=2*M.length := by
  induction M with
  | nil => simp [pairingLabels]
  | cons a M ih =>
    simp only [pairingLabels] at ih
    simp only [pairingLabels,List.flatMap_cons,List.length_append,List.length_cons,List.length_nil]
    omega

theorem pairingLabels_get_zero (M : List (α × α)) (i : Fin M.length) :
    (pairingLabels M)[2*i.val]'(by rw [pairingLabels_length]; omega) = (M[i.val]).1 := by
  induction M with
  | nil => exact Fin.elim0 i
  | cons p M ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [pairingLabels]
    · have he : 2*(j.val+1)=2*j.val+2 := by omega
      simpa only [Fin.val_succ,he,pairingLabels,List.flatMap_cons,List.cons_append,
        List.nil_append,List.getElem_cons_succ] using ih j

theorem pairingLabels_get_one (M : List (α × α)) (i : Fin M.length) :
    (pairingLabels M)[2*i.val+1]'(by rw [pairingLabels_length]; omega) = (M[i.val]).2 := by
  induction M with
  | nil => exact Fin.elim0 i
  | cons p M ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [pairingLabels]
    · have he : 2*(j.val+1)+1=(2*j.val+1)+2 := by omega
      simpa only [Fin.val_succ,he,pairingLabels,List.flatMap_cons,List.cons_append,
        List.nil_append,List.getElem_cons_succ] using ih j

/-- The first-row matching recursion covers the literal full coordinate list. -/
def matchingCoordinateEquiv {n : ℕ} (M : List (Fin (2*n) × Fin (2*n)))
    (hM : M ∈ perfectPairings n (List.finRange (2*n))) : (Fin n × Fin 2) ≃ Fin (2*n) := by
  have hp := perfectPairings_labels_perm n (List.finRange (2*n)) (by simp) M hM
  have hlen : (pairingLabels M).length=n*2 := by
    rw [hp.length_eq,List.length_finRange]
    omega
  have hnodup : (pairingLabels M).Nodup := hp.nodup_iff.mpr (List.nodup_finRange _)
  have hall : ∀ i : Fin (2*n), i ∈ pairingLabels M := fun i => hp.mem_iff.mpr (List.mem_finRange i)
  exact (finProdFinEquiv.trans (finCongr hlen.symm)).trans
    (List.Nodup.getEquivOfForallMemList (pairingLabels M) hnodup hall)

def matchingEntry {n : ℕ} (M : List (Fin (2*n) × Fin (2*n)))
    (hM : M ∈ perfectPairings n (List.finRange (2*n))) (i : Fin n) : Fin (2*n) × Fin (2*n) :=
  M.get (Fin.cast (perfectPairings_length_of_mem n _ M hM).symm i)

theorem matchingCoordinateEquiv_zero {n : ℕ} (M : List (Fin (2*n) × Fin (2*n)))
    (hM : M ∈ perfectPairings n (List.finRange (2*n))) (i : Fin n) :
    matchingCoordinateEquiv M hM (i,0) = (matchingEntry M hM i).1 := by
  have h := pairingLabels_get_zero M (Fin.cast (perfectPairings_length_of_mem n _ M hM).symm i)
  simpa only [matchingCoordinateEquiv,matchingEntry,Equiv.trans_apply,finProdFinEquiv,
    List.Nodup.getEquivOfForallMemList,Equiv.coe_fn_mk,finCongr,Fin.val_cast,List.get_eq_getElem,
    Fin.val_zero,Nat.add_zero,Nat.zero_add,Nat.mul_comm] using h

theorem matchingCoordinateEquiv_one {n : ℕ} (M : List (Fin (2*n) × Fin (2*n)))
    (hM : M ∈ perfectPairings n (List.finRange (2*n))) (i : Fin n) :
    matchingCoordinateEquiv M hM (i,1) = (matchingEntry M hM i).2 := by
  have h := pairingLabels_get_one M (Fin.cast (perfectPairings_length_of_mem n _ M hM).symm i)
  simpa only [matchingCoordinateEquiv,matchingEntry,Equiv.trans_apply,finProdFinEquiv,
    List.Nodup.getEquivOfForallMemList,Equiv.coe_fn_mk,finCongr,Fin.val_cast,List.get_eq_getElem,
    Fin.val_one,Nat.mul_comm,Nat.add_comm] using h

theorem pairingWeight_eq_prod_entries {n : ℕ} (M : List (Fin (2*n) × Fin (2*n)))
    (hM : M ∈ perfectPairings n (List.finRange (2*n))) (w : Fin (2*n) → Fin (2*n) → ℝ) :
    pairingWeight w M = ∏ i : Fin n, w (matchingEntry M hM i).1 (matchingEntry M hM i).2 := by
  unfold pairingWeight
  have hlen := perfectPairings_length_of_mem n _ M hM
  calc
    _ = ∏ i : Fin M.length, w (M.get i).1 (M.get i).2 := by
      conv_lhs => rw [← List.ofFn_get M,List.map_ofFn,List.prod_ofFn]
      rfl
    _ = _ := Fintype.prod_equiv (finCongr hlen) _ _ (by
      intro i
      simp [matchingEntry])

end
end IsingBulk.Tail
