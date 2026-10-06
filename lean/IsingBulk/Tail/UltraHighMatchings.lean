import IsingBulk.Algebra.SchurContinuation
import Mathlib.Tactic

/-! The full all-size matching expansion norm bound. No Hadamard bound
or numerical finite-size verification is used. -/
namespace IsingBulk.Tail
noncomputable section

def matchingCount : ℕ → ℕ
  | 0 => 1
  | n+1 => (2*n+1)*matchingCount n

 theorem matchingCount_factorial (n : ℕ) :
    matchingCount n*(2^n*n.factorial) = (2*n).factorial := by
  induction n with
  | zero => simp [matchingCount]
  | succ n ih =>
    have he : 2*(n+1) = (2*n+1)+1 := by omega
    rw [he, Nat.factorial_succ, Nat.factorial_succ, matchingCount,
      pow_succ, Nat.factorial_succ, ← ih]
    ring

theorem matchingCount_le_pow (n : ℕ) : matchingCount n ≤ (2*n)^n := by
  induction n with
  | zero => simp [matchingCount]
  | succ n ih =>
    rw [matchingCount, pow_succ]
    calc
      (2*n+1)*matchingCount n ≤ (2*(n+1))*(2*n)^n :=
        Nat.mul_le_mul (by omega) ih
      _ ≤ (2*(n+1))*(2*(n+1))^n :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) n)
      _ = (2*(n+1))^n*(2*(n+1)) := by ring

 theorem list_sum_norm_le_length {α : Type*} (xs : List α) (f : α → ℂ) (B : ℝ)
    (hf : ∀ x ∈ xs, ‖f x‖ ≤ B) : ‖(xs.map f).sum‖ ≤ xs.length*B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    calc
      ‖f x+(xs.map f).sum‖ ≤ ‖f x‖+‖(xs.map f).sum‖ := norm_add_le _ _
      _ ≤ B+xs.length*B := add_le_add (hf x (by simp))
        (ih (fun y hy => hf y (by simp [hy])))
      _ = (xs.length+1)*B := by ring

theorem pfaffian_norm_le_matchings (A : ℂ → ℂ → ℂ) (n : ℕ) (xs : List ℂ)
    (hlen : xs.length = 2*n) {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ a ∈ xs, ∀ b ∈ xs, ‖A a b‖ ≤ C) :
    ‖IsingBulk.Schur.pfaffian A n xs‖ ≤ (matchingCount n:ℝ)*C^n := by
  induction n generalizing xs with
  | zero => simp [IsingBulk.Schur.pfaffian, matchingCount]
  | succ n ih =>
    cases xs with
    | nil => simp at hlen
    | cons a xs =>
      have hlen' : xs.length = 2*n+1 := by simp only [List.length_cons] at hlen; omega
      rw [IsingBulk.Schur.pfaffian]
      have hb : ∀ bj ∈ xs.zipIdx,
          ‖(-1:ℂ)^bj.2*A a bj.1*IsingBulk.Schur.pfaffian A n (xs.eraseIdx bj.2)‖ ≤
            C*((matchingCount n:ℝ)*C^n) := by
        intro bj hbj
        have hj := (List.mem_zipIdx' hbj).1
        have hmem : bj.1 ∈ xs := by
          rw [(List.mem_zipIdx' hbj).2]
          exact List.getElem_mem hj
        have herase : (xs.eraseIdx bj.2).length=2*n := by
          rw [List.length_eraseIdx_of_lt hj, hlen']; omega
        have hsub : ∀ b ∈ xs.eraseIdx bj.2, b ∈ a::xs := by
          intro b hb
          exact List.mem_cons_of_mem a (List.mem_of_mem_eraseIdx hb)
        have hi := ih (xs.eraseIdx bj.2) herase (fun b hb c hc => hA b (hsub b hb) c (hsub c hc))
        rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
        exact mul_le_mul (hA a (by simp) bj.1 (by simp [hmem])) hi (norm_nonneg _) hC
      have hh := list_sum_norm_le_length xs.zipIdx
        (fun bj => (-1:ℂ)^bj.2*A a bj.1*IsingBulk.Schur.pfaffian A n (xs.eraseIdx bj.2)) _ hb
      apply hh.trans
      simp only [List.length_zipIdx, hlen', matchingCount, Nat.cast_mul, Nat.cast_add,
        Nat.cast_ofNat, Nat.cast_one, pow_succ]
      ring_nf
      rfl

theorem pfaffian_norm_le_power (A : ℂ → ℂ → ℂ) (n : ℕ) (xs : List ℂ)
    (hlen : xs.length=2*n) {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ a ∈ xs, ∀ b ∈ xs, ‖A a b‖ ≤ C) :
    ‖IsingBulk.Schur.pfaffian A n xs‖ ≤ ((2*n:ℕ):ℝ)^n*C^n := by
  apply (pfaffian_norm_le_matchings A n xs hlen hC hA).trans
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast matchingCount_le_pow n) (pow_nonneg hC n)

end
end IsingBulk.Tail
