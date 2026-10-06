import IsingBulk.Tail.AllBranchExteriorPoleAbsorption

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets Set
open scoped ContDiff

theorem allBranchExterior_norm_list_div (L : List ℝ) (z A : ℝ) (hz : 0 ≤ z)
    (h : ∀ x ∈ L, ‖x‖/z ≤ A) : ‖L.sum‖/z ≤ (L.length:ℝ)*A := by
  induction L with
  | nil => simp
  | cons x L ih =>
    have hx := h x (by simp)
    have hL := ih (fun y hy => h y (by simp [hy]))
    have hh := div_le_div_of_nonneg_right (norm_add_le x L.sum) hz
    simp only [List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    rw [add_div] at hh
    nlinarith

theorem allBranchExterior_weighted_pole_bound {N : ℕ}
    (f g : (Fin N → ℝ) → ℝ) {U : Set (Fin N → ℝ)} (hU : IsOpen U)
    (hf : ∀ x ∈ U, ContDiffAt ℝ ∞ f x) (hg : ∀ x ∈ U, ContDiffAt ℝ ∞ g x)
    (u : Fin N → ℝ) (hu : u ∈ U) (l : List (Fin N)) (m : ℕ)
    (d z A B : ℝ) (hd : 0 < d) (hz : 0 ≤ z) (hA : 0 ≤ A) ( _hB : 0 ≤ B)
    (hfj : ∀ k : List (Fin N), k.length ≤ l.length → ‖cutoffJet k f u‖/z^m ≤ A/d^(m+k.length))
    (hgj : ∀ k : List (Fin N), k.length ≤ l.length → ‖cutoffJet k g u‖ ≤ B/d^k.length) :
    ‖cutoffJet l (fun x => f x*g x) u‖/z^m ≤ (2:ℝ)^l.length*A*B/d^(m+l.length) := by
  rw [cutoffJet_product_word l f g hU hf hg u hu]
  have ht : ∀ p ∈ cutoffWordSplits l,
      ‖cutoffJet p.1 f u*cutoffJet p.2 g u‖/z^m ≤ A*B/d^(m+l.length) := by
    intro p hp
    have hlen := cutoffWordSplits_orders l p hp
    rw [norm_mul]
    calc
      _ = (‖cutoffJet p.1 f u‖/z^m)*‖cutoffJet p.2 g u‖ := by ring
      _ ≤ (A/d^(m+p.1.length))*(B/d^p.2.length) :=
        mul_le_mul (hfj p.1 (by omega)) (hgj p.2 (by omega)) (norm_nonneg _) (by positivity)
      _ = _ := by
        rw [div_mul_div_comm,← pow_add]
        congr 2
        omega
  have hh := allBranchExterior_norm_list_div
    ((cutoffWordSplits l).map (fun p => cutoffJet p.1 f u*cutoffJet p.2 g u)) (z^m)
    (A*B/d^(m+l.length)) (pow_nonneg hz _) (by
      intro x hx
      obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hx
      exact ht p hp)
  rw [List.length_map,cutoffWordSplits_length,Nat.cast_pow,Nat.cast_ofNat] at hh
  apply hh.trans_eq
  ring

end
end IsingBulk.Tail
