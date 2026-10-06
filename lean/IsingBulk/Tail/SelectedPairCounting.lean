import IsingBulk.Tail.PfaffianPairings
import IsingBulk.Tail.SelectedContourArithmetic
import Mathlib.Tactic

/-! Compact-coordinate accounting for the full matching expansion in F.
The count is on actual pairing labels, not an independence assumption. -/
namespace IsingBulk.Tail
noncomputable section

 def compactLabelCount {α : Type*} (c : α → Bool) (xs : List α) : ℕ := (xs.filter c).length
 def compactPairCount {α : Type*} (c : α → Bool) (M : List (α × α)) : ℕ :=
  (M.filter (fun p => c p.1 && c p.2)).length

 theorem twice_compactPairCount_le {α : Type*} (c : α → Bool) (M : List (α × α)) :
    2*compactPairCount c M ≤ compactLabelCount c (pairingLabels M) := by
  induction M with
  | nil => simp [compactPairCount,compactLabelCount,pairingLabels]
  | cons p M ih =>
    rcases p with ⟨a,b⟩
    cases ha : c a <;> cases hb : c b <;>
      simp [compactPairCount,compactLabelCount,pairingLabels,ha,hb] at * <;> omega

 theorem perfectPairing_compact_count {α : Type*} (c : α → Bool) (n : ℕ) (xs : List α)
    (hlen : xs.length=2*n) (M : List (α × α)) (hM : M ∈ perfectPairings n xs) :
    2*compactPairCount c M ≤ compactLabelCount c xs := by
  have hh := twice_compactPairCount_le c M
  have hp := (perfectPairings_labels_perm n xs hlen M hM).filter c
  rw [show compactLabelCount c (pairingLabels M) = compactLabelCount c xs from hp.length_eq] at hh
  exact hh

 theorem exceptional_pairing_cost {α : Type*} (c : α → Bool) (H : ℝ) (M : List (α × α)) :
    pairingWeight (fun a b => if c a && c b then H else 1) M = H^(compactPairCount c M) := by
  induction M with
  | nil => simp [pairingWeight,compactPairCount]
  | cons p M ih =>
    rcases p with ⟨a,b⟩
    cases ha : c a <;> cases hb : c b <;>
      simp_all [pairingWeight,compactPairCount,pow_succ,mul_comm]

 theorem exceptional_pairing_cost_le {α : Type*} (c : α → Bool) {H : ℝ} (hH : 1 ≤ H)
    (n : ℕ) (xs : List α) (hlen : xs.length=2*n) (M : List (α × α))
    (hM : M ∈ perfectPairings n xs) :
    pairingWeight (fun a b => if c a && c b then H else 1) M ≤ H^(compactLabelCount c xs) := by
  rw [exceptional_pairing_cost]
  apply pow_le_pow_right₀ hH
  have hh := perfectPairing_compact_count c n xs hlen M hM
  omega

 theorem pairingMajorant_exceptional_le {α : Type*} (c : α → Bool) {H : ℝ} (hH : 1 ≤ H)
    (n : ℕ) (xs : List α) (hlen : xs.length=2*n) :
    pairingMajorant (fun a b => if c a && c b then H else 1) n xs ≤
      (matchingCount n:ℝ)*H^(compactLabelCount c xs) := by
  unfold pairingMajorant
  calc
    _ ≤ ((perfectPairings n xs).map (fun _ => H^(compactLabelCount c xs))).sum := by
      apply List.sum_le_sum
      intro M hM
      exact exceptional_pairing_cost_le c hH n xs hlen M hM
    _ = (matchingCount n:ℝ)*H^(compactLabelCount c xs) := by
      simp [perfectPairings_card n xs hlen]

 def compactDiscountWeight {α : Type*} (c : α → Bool) (L : ℝ) (xs : List α) : ℝ :=
  (xs.map (fun i => if c i then L⁻¹ else 1)).prod

 theorem compactDiscountWeight_eq {α : Type*} (c : α → Bool) (L : ℝ) (xs : List α) :
    compactDiscountWeight c L xs = (L⁻¹)^(compactLabelCount c xs) := by
  induction xs with
  | nil => simp [compactDiscountWeight,compactLabelCount]
  | cons a xs ih =>
    cases ha : c a <;>
      simp_all [compactDiscountWeight,compactLabelCount,pow_succ,mul_comm]

 theorem gaussian_compact_discount {α : Type*} (c : α → Bool) {a L : ℝ}
    (ha : 0 < a) (hL : 0 < L) (xs : List α) :
    Real.exp (-a*(compactLabelCount c xs:ℝ)^2) ≤
      Real.exp ((Real.log L)^2/(4*a))*compactDiscountWeight c L xs := by
  rw [compactDiscountWeight_eq,inv_pow,← div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos hL _)).mpr
  simpa only [mul_comm] using compact_assignment_penalty ha hL (compactLabelCount c xs)

end
end IsingBulk.Tail
