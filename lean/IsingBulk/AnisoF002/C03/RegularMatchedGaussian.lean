import IsingBulk.AnisoF002.C03.RegularMatchedSummation
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Gaussian envelopes for the exact matching majorants

Replacing the strict Schur constant q by sqrt(q) leaves a summable exact
matching majorant after extracting q^(n²).  Boundedness of that positive
summable majorant gives a Gaussian bound for every index, without a
Stirling approximation or a cutoff in the physical particle series.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open scoped BigOperators

theorem evenMatchedBound_extract_square {A C q h : ℝ} (hh : h ≠ 0) (hs : h ^ 2 = q)
    (n : ℕ) :
    evenMatchedBound (A / h) C h n * q ^ (n ^ 2) = evenMatchedBound A C q n := by
  have hp : h ^ (2 * n * (n - 1)) * q ^ (n ^ 2) / h ^ (2 * n) =
      q ^ (2 * n * (n - 1)) := by
    apply (div_eq_iff (pow_ne_zero _ hh)).mpr
    rw [← hs]
    simp only [← pow_mul, ← pow_add]
    congr 1
    cases n with
    | zero => simp
    | succ n => simp only [Nat.succ_sub_one]; ring
  calc
    evenMatchedBound (A / h) C h n * q ^ (n ^ 2) =
        A ^ (2 * n) * ((matchingNumber n : ℝ) * C ^ n) *
          (h ^ (2 * n * (n - 1)) * q ^ (n ^ 2) / h ^ (2 * n)) := by
      unfold evenMatchedBound
      rw [div_pow]
      ring
    _ = evenMatchedBound A C q n := by rw [hp]; unfold evenMatchedBound; ring

theorem oddMatchedBound_extract_square {A C q h : ℝ} (hs : h ^ 2 = q)
    (n : ℕ) :
    oddMatchedBound A C h n * q ^ (n ^ 2) = oddMatchedBound A C q n := by
  have hp : h ^ (2 * n * n) * q ^ (n ^ 2) = q ^ (2 * n * n) := by
    rw [← hs]
    simp only [← pow_mul, ← pow_add]
    congr 1
    ring
  unfold oddMatchedBound
  linear_combination A ^ (2 * n + 1) * ((matchingNumber (n + 1) : ℝ) * C ^ n) * hp

theorem evenMatchedBound_square_envelope {A C q : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hq : 0 < q) (hq1 : q < 1) :
    ∃ M : ℝ, 0 < M ∧ ∀ n : ℕ, evenMatchedBound A C q n ≤ M * q ^ (n ^ 2) := by
  let h := Real.sqrt q
  have hh : 0 < h := Real.sqrt_pos.mpr hq
  have hs : h ^ 2 = q := Real.sq_sqrt hq.le
  have hh1 : h < 1 := by nlinarith
  have hsum := summable_evenMatchedBound_polynomial (div_nonneg hA hh.le) hC hh.le hh1 0
  simp only [pow_zero, one_mul] at hsum
  have hnonneg : ∀ n : ℕ, 0 ≤ evenMatchedBound (A / h) C h n := by
    intro n
    unfold evenMatchedBound
    positivity
  let M := (∑' n : ℕ, evenMatchedBound (A / h) C h n) + 1
  have hM : 0 < M := by
    have ht : 0 ≤ ∑' n : ℕ, evenMatchedBound (A / h) C h n := tsum_nonneg hnonneg
    dsimp [M]
    linarith
  refine ⟨M, hM, ?_⟩
  intro n
  rw [← evenMatchedBound_extract_square hh.ne' hs n]
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hq.le _)
  exact (hsum.le_tsum n (fun k _ => hnonneg k)).trans (by dsimp [M]; linarith)

theorem oddMatchedBound_square_envelope {A C q : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hq : 0 < q) (hq1 : q < 1) :
    ∃ M : ℝ, 0 < M ∧ ∀ n : ℕ, oddMatchedBound A C q n ≤ M * q ^ (n ^ 2) := by
  let h := Real.sqrt q
  have hh : 0 < h := Real.sqrt_pos.mpr hq
  have hs : h ^ 2 = q := Real.sq_sqrt hq.le
  have hh1 : h < 1 := by nlinarith
  have hsum := summable_oddMatchedBound_polynomial hA hC hh.le hh1 0
  simp only [pow_zero, one_mul] at hsum
  have hnonneg : ∀ n : ℕ, 0 ≤ oddMatchedBound A C h n := by
    intro n
    unfold oddMatchedBound
    positivity
  let M := (∑' n : ℕ, oddMatchedBound A C h n) + 1
  have hM : 0 < M := by
    have ht : 0 ≤ ∑' n : ℕ, oddMatchedBound A C h n := tsum_nonneg hnonneg
    dsimp [M]
    linarith
  refine ⟨M, hM, ?_⟩
  intro n
  rw [← oddMatchedBound_extract_square hs n]
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hq.le _)
  exact (hsum.le_tsum n (fun k _ => hnonneg k)).trans (by dsimp [M]; linarith)

theorem q_square_le_particle_gaussian {q V : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (n : ℕ) (hV : 0 ≤ V) (hVn : V ≤ 2 * (n : ℝ) + 1) :
    q ^ (n ^ 2) ≤ (1 / q) * Real.exp ((Real.log q / 8) * V ^ 2) := by
  have hlog : Real.log q < 0 := Real.log_neg hq hq1
  have hsq : V ^ 2 ≤ (2 * (n : ℝ) + 1) ^ 2 := pow_le_pow_left₀ hV hVn 2
  have hquad : V ^ 2 / 8 - 1 ≤ (n : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((n : ℝ) - 1 / 2)]
  have he : (n : ℝ) ^ 2 * Real.log q ≤ -Real.log q + (Real.log q / 8) * V ^ 2 := by
    nlinarith [mul_le_mul_of_nonpos_right hquad hlog.le]
  calc
    q ^ (n ^ 2) = Real.exp ((n : ℝ) ^ 2 * Real.log q) := by
      rw [← Nat.cast_pow, ← Real.log_pow, Real.exp_log (pow_pos hq _)]
    _ ≤ Real.exp (-Real.log q + (Real.log q / 8) * V ^ 2) := Real.exp_le_exp.mpr he
    _ = (1 / q) * Real.exp ((Real.log q / 8) * V ^ 2) := by
      rw [Real.exp_add, Real.exp_neg, Real.exp_log hq, one_div]

/-- A common positive Gaussian rate and a common positive constant cover
every even and every odd complete matching bound, including small indices. -/
theorem exists_matched_gaussian {A C q : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hq : 0 < q) (hq1 : q < 1) :
    ∃ M kappa : ℝ, 0 < M ∧ 0 < kappa ∧ ∀ n : ℕ,
      evenMatchedBound A C q n ≤ M * Real.exp (-kappa * (2 * (n : ℝ)) ^ 2) ∧
      oddMatchedBound A C q n ≤ M * Real.exp (-kappa * (2 * (n : ℝ) + 1) ^ 2) := by
  obtain ⟨Me, hMe, hbe⟩ := evenMatchedBound_square_envelope hA hC hq hq1
  obtain ⟨Mo, hMo, hbo⟩ := oddMatchedBound_square_envelope hA hC hq hq1
  let M := max Me Mo / q
  let kappa := -Real.log q / 8
  have hM : 0 < M := div_pos (lt_of_lt_of_le hMe (le_max_left _ _)) hq
  have hk : 0 < kappa := div_pos (neg_pos.mpr (Real.log_neg hq hq1)) (by norm_num)
  refine ⟨M, kappa, hM, hk, ?_⟩
  intro n
  have he := q_square_le_particle_gaussian hq hq1 n
    (show 0 ≤ 2 * (n : ℝ) by positivity) (by linarith : 2 * (n : ℝ) ≤ 2 * n + 1)
  have ho := q_square_le_particle_gaussian hq hq1 n
    (show 0 ≤ 2 * (n : ℝ) + 1 by positivity) le_rfl
  constructor
  · calc
      evenMatchedBound A C q n ≤ Me * q ^ (n ^ 2) := hbe n
      _ ≤ max Me Mo * ((1 / q) * Real.exp ((Real.log q / 8) * (2 * (n : ℝ)) ^ 2)) :=
        mul_le_mul (le_max_left _ _) he (pow_nonneg hq.le _) (le_trans hMe.le (le_max_left _ _))
      _ = M * Real.exp (-kappa * (2 * (n : ℝ)) ^ 2) := by
        dsimp [M, kappa]
        rw [neg_div, neg_neg]
        ring
  · calc
      oddMatchedBound A C q n ≤ Mo * q ^ (n ^ 2) := hbo n
      _ ≤ max Me Mo * ((1 / q) * Real.exp ((Real.log q / 8) * (2 * (n : ℝ) + 1) ^ 2)) :=
        mul_le_mul (le_max_right _ _) ho (pow_nonneg hq.le _) (le_trans hMo.le (le_max_right _ _))
      _ = M * Real.exp (-kappa * (2 * (n : ℝ) + 1) ^ 2) := by
        dsimp [M, kappa]
        rw [neg_div, neg_neg]
        ring

end
end IsingBulk.AnisoF002.RegularTail.C03
