import IsingBulk.Tail.UltraHighMatchings
import Mathlib.Data.List.Perm.Basic

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.Tail

 theorem pairProduct_norm_perm (K : ℂ → ℂ → ℂ)
    (hsym : ∀ a b, ‖K a b‖=‖K b a‖) {xs ys : List ℂ} (hp : xs.Perm ys) :
    ‖IsingBulk.Schur.pairProduct K xs‖=‖IsingBulk.Schur.pairProduct K ys‖ := by
  induction hp with
  | nil => rfl
  | cons a hp ih =>
    simp only [IsingBulk.Schur.pairProduct,norm_mul]
    rw [(hp.map (K a)).prod_eq,ih]
  | swap a b xs =>
    simp only [IsingBulk.Schur.pairProduct,List.map_cons,List.prod_cons,norm_mul]
    rw [hsym b a]
    ring
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem list_kernel_product_bound (K : ℂ → ℂ → ℂ) (a : ℂ) (xs : List ℂ)
    {r : ℝ} (hr : 0 ≤ r) (hK : ∀ b ∈ xs, ‖K a b‖ ≤ r) :
    ‖(xs.map (K a)).prod‖ ≤ r^xs.length := by
  induction xs with
  | nil => simp
  | cons b xs ih =>
    simp only [List.map_cons,List.prod_cons,List.length_cons,norm_mul,pow_succ]
    have hh := mul_le_mul (hK b (by simp)) (ih (fun c hc => hK c (by simp [hc])))
      (norm_nonneg _) hr
    simpa only [mul_comm] using hh

/-- Matching the second kernel never divides by a first-kernel factor.
This retains the full unmatched-pair contraction, including coincident roots. -/
theorem matched_pfaffian_bound (K L : ℂ → ℂ → ℂ)
    (hsym : ∀ a b, ‖K a b‖=‖K b a‖) (n : ℕ) (xs : List ℂ)
    (hlen : xs.length=2*n) {r C : ℝ} (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hK : ∀ a ∈ xs, ∀ b ∈ xs, ‖K a b‖ ≤ r)
    (hKL : ∀ a ∈ xs, ∀ b ∈ xs, ‖K a b*L a b‖ ≤ C) :
    ‖IsingBulk.Schur.pairProduct K xs*IsingBulk.Schur.pfaffian L n xs‖ ≤
      (matchingCount n:ℝ)*C^n*r^(2*n*(n-1)) := by
  induction n generalizing xs with
  | zero =>
    have he : xs=[] := List.length_eq_zero_iff.mp (by simpa using hlen)
    subst xs
    simp [IsingBulk.Schur.pairProduct,IsingBulk.Schur.pfaffian,matchingCount]
  | succ n ih =>
    cases xs with
    | nil => simp at hlen
    | cons a xs =>
      have hlen' : xs.length=2*n+1 := by simp only [List.length_cons] at hlen; omega
      let P := IsingBulk.Schur.pairProduct K (a::xs)
      have hb : ∀ bj ∈ xs.zipIdx,
          ‖P*((-1:ℂ)^bj.2*L a bj.1*IsingBulk.Schur.pfaffian L n (xs.eraseIdx bj.2))‖ ≤
          C*r^(4*n)*((matchingCount n:ℝ)*C^n*r^(2*n*(n-1))) := by
        intro bj hbj
        have hj := (List.mem_zipIdx' hbj).1
        have hmem : bj.1 ∈ xs := by
          rw [(List.mem_zipIdx' hbj).2]
          exact List.getElem_mem hj
        have hperm : (bj.1::xs.eraseIdx bj.2).Perm xs := by
          rw [(List.mem_zipIdx' hbj).2]
          exact List.getElem_cons_eraseIdx_perm hj
        have herase : (xs.eraseIdx bj.2).length=2*n := by
          rw [List.length_eraseIdx_of_lt hj,hlen']; omega
        have hsub : ∀ b ∈ xs.eraseIdx bj.2, b ∈ a::xs :=
          fun b hb => List.mem_cons_of_mem a (List.mem_of_mem_eraseIdx hb)
        have hi := ih (xs.eraseIdx bj.2) herase
          (fun b hb c hc => hK b (hsub b hb) c (hsub c hc))
          (fun b hb c hc => hKL b (hsub b hb) c (hsub c hc))
        have hprodA := list_kernel_product_bound K a (xs.eraseIdx bj.2) hr
          (fun b hb => hK a (by simp) b (hsub b hb))
        have hprodB := list_kernel_product_bound K bj.1 (xs.eraseIdx bj.2) hr
          (fun b hb => hK bj.1 (by simp [hmem]) b (hsub b hb))
        rw [herase] at hprodA hprodB
        have hp : ‖P‖ = ‖K a bj.1‖*‖((xs.eraseIdx bj.2).map (K a)).prod‖*
            ‖((xs.eraseIdx bj.2).map (K bj.1)).prod‖*
            ‖IsingBulk.Schur.pairProduct K (xs.eraseIdx bj.2)‖ := by
          have hh := pairProduct_norm_perm K hsym (List.Perm.cons a hperm)
          dsimp [P]
          rw [← hh]
          simp only [IsingBulk.Schur.pairProduct,List.map_cons,List.prod_cons,norm_mul]
          ring
        simp only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul]
        rw [hp]
        have hpair := hKL a (by simp) bj.1 (by simp [hmem])
        rw [norm_mul] at hpair
        rw [norm_mul] at hi
        have hh := mul_le_mul
          (mul_le_mul (mul_le_mul hpair hprodA (norm_nonneg _) hC) hprodB
            (norm_nonneg _) (mul_nonneg hC (pow_nonneg hr _))) hi
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
        convert hh using 1
        · ring
        · rw [show 4*n=2*n+2*n by omega,pow_add]
          ring
      have hh := list_sum_norm_le_length xs.zipIdx
        (fun bj => P*((-1:ℂ)^bj.2*L a bj.1*IsingBulk.Schur.pfaffian L n (xs.eraseIdx bj.2))) _ hb
      have he : 2*n*(n-1)+4*n=2*(n+1)*n := by
        cases n with
        | zero => simp
        | succ n => simp only [Nat.succ_sub_one]; ring
      simp only [List.length_zipIdx,hlen'] at hh
      unfold IsingBulk.Schur.pfaffian
      rw [← List.sum_map_mul_left]
      change ‖(xs.zipIdx.map (fun bj => P*((-1:ℂ)^bj.2*L a bj.1*IsingBulk.Schur.pfaffian L n (xs.eraseIdx bj.2)))).sum‖ ≤ _
      apply hh.trans_eq
      simp only [matchingCount,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one,pow_succ,Nat.succ_sub_one]
      rw [← he,pow_add]
      ring
/-- A unit ghost row costs no root contraction and leaves exactly `2*n^2`
unmatched physical root factors. The ghost itself is not a physical particle. -/
theorem odd_matched_pfaffian_bound (K L : ℂ → ℂ → ℂ)
    (hsym : ∀ a b, ‖K a b‖=‖K b a‖) (n : ℕ) (g : ℂ) (xs : List ℂ)
    (hlen : xs.length=2*n+1) {r C : ℝ} (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hK : ∀ a ∈ xs, ∀ b ∈ xs, ‖K a b‖ ≤ r)
    (hKL : ∀ a ∈ xs, ∀ b ∈ xs, ‖K a b*L a b‖ ≤ C)
    (hg : ∀ b ∈ xs, ‖L g b‖ ≤ 1) :
    ‖IsingBulk.Schur.pairProduct K xs*IsingBulk.Schur.pfaffian L (n+1) (g::xs)‖ ≤
      (matchingCount (n+1):ℝ)*C^n*r^(2*n*n) := by
  let P := IsingBulk.Schur.pairProduct K xs
  have hb : ∀ bj ∈ xs.zipIdx,
      ‖P*((-1:ℂ)^bj.2*L g bj.1*IsingBulk.Schur.pfaffian L n (xs.eraseIdx bj.2))‖ ≤
      r^(2*n)*((matchingCount n:ℝ)*C^n*r^(2*n*(n-1))) := by
    intro bj hbj
    have hj := (List.mem_zipIdx' hbj).1
    have hmem : bj.1 ∈ xs := by
      rw [(List.mem_zipIdx' hbj).2]
      exact List.getElem_mem hj
    have hperm : (bj.1::xs.eraseIdx bj.2).Perm xs := by
      rw [(List.mem_zipIdx' hbj).2]
      exact List.getElem_cons_eraseIdx_perm hj
    have herase : (xs.eraseIdx bj.2).length=2*n := by
      rw [List.length_eraseIdx_of_lt hj,hlen]; omega
    have hsub : ∀ b ∈ xs.eraseIdx bj.2, b ∈ xs := fun _ hb => List.mem_of_mem_eraseIdx hb
    have hi := matched_pfaffian_bound K L hsym n (xs.eraseIdx bj.2) herase hr hC
      (fun b hb c hc => hK b (hsub b hb) c (hsub c hc))
      (fun b hb c hc => hKL b (hsub b hb) c (hsub c hc))
    have hprod := list_kernel_product_bound K bj.1 (xs.eraseIdx bj.2) hr
      (fun b hb => hK bj.1 hmem b (hsub b hb))
    rw [herase] at hprod
    have hp : ‖P‖ = ‖((xs.eraseIdx bj.2).map (K bj.1)).prod‖*
        ‖IsingBulk.Schur.pairProduct K (xs.eraseIdx bj.2)‖ := by
      dsimp [P]
      rw [← pairProduct_norm_perm K hsym hperm]
      simp only [IsingBulk.Schur.pairProduct,norm_mul]
    simp only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul]
    rw [hp]
    rw [norm_mul] at hi
    have hh := mul_le_mul (mul_le_mul hprod (hg bj.1 hmem) (norm_nonneg _) (pow_nonneg hr _))
      hi (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
    simpa only [mul_one] using (show
      ‖(List.map (K bj.1) (xs.eraseIdx bj.2)).prod‖ *
      ‖IsingBulk.Schur.pairProduct K (xs.eraseIdx bj.2)‖ *
      (‖L g bj.1‖ * ‖IsingBulk.Schur.pfaffian L n (xs.eraseIdx bj.2)‖) ≤
      (r^(2*n)*1)*((matchingCount n:ℝ)*C^n*r^(2*n*(n-1))) by
        convert hh using 1; ring)
  have hh := list_sum_norm_le_length xs.zipIdx
    (fun bj => P*((-1:ℂ)^bj.2*L g bj.1*IsingBulk.Schur.pfaffian L n (xs.eraseIdx bj.2))) _ hb
  simp only [List.length_zipIdx,hlen] at hh
  unfold IsingBulk.Schur.pfaffian
  rw [← List.sum_map_mul_left]
  change ‖(xs.zipIdx.map (fun bj => P*((-1:ℂ)^bj.2*L g bj.1*IsingBulk.Schur.pfaffian L n (xs.eraseIdx bj.2)))).sum‖ ≤ _
  apply hh.trans_eq
  have he : 2*n*(n-1)+2*n=2*n*n := by
    cases n with
    | zero => simp
    | succ n => simp only [Nat.succ_sub_one]; ring
  simp only [matchingCount,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one]
  rw [← he,pow_add]
  ring
end
end IsingBulk.Anisotropic.RegularEdges
