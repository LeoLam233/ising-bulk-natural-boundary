import IsingBulk.AnisoF002.C03.RegularRetainedJets
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Summability of the exact complete matched numerator bounds

These are the explicit bounds proved for the actual full and retained
numerators, not replacement physical functions.  Their exact recurrences
show summability after every fixed polynomial derivative loss, including
all complementary particle indices and the retained cross-pair cost.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Filter
open scoped Topology

def evenMatchedBound (A C q : ℝ) (n : ℕ) : ℝ :=
  A ^ (2 * n) * ((matchingNumber n : ℝ) * C ^ n * q ^ (2 * n * (n - 1)))

def oddMatchedBound (A C q : ℝ) (n : ℕ) : ℝ :=
  A ^ (2 * n + 1) * ((matchingNumber (n + 1) : ℝ) * C ^ n * q ^ (2 * n * n))

theorem evenMatchedBound_succ (A C q : ℝ) (n : ℕ) :
    evenMatchedBound A C q (n + 1) =
      (A ^ 2 * C * (2 * (n : ℝ) + 1) * q ^ (4 * n)) * evenMatchedBound A C q n := by
  have he : 2 * (n + 1) * ((n + 1) - 1) = 2 * n * (n - 1) + 4 * n := by
    cases n with
    | zero => norm_num
    | succ n => simp only [Nat.succ_sub_one]; ring
  have ha : 2 * (n + 1) = 2 * n + 2 := by ring
  simp only [evenMatchedBound]
  rw [he, ha]
  simp only [matchingNumber, pow_add, pow_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  ring

theorem oddMatchedBound_succ (A C q : ℝ) (n : ℕ) :
    oddMatchedBound A C q (n + 1) =
      (A ^ 2 * C * (2 * (n : ℝ) + 3) * q ^ (4 * n + 2)) * oddMatchedBound A C q n := by
  have he : 2 * (n + 1) * (n + 1) = 2 * n * n + (4 * n + 2) := by ring
  have ha : 2 * (n + 1) + 1 = (2 * n + 1) + 2 := by ring
  simp only [oddMatchedBound, matchingNumber, he, ha, pow_add, pow_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  ring

theorem summable_polynomial_of_nonnegative_recurrence (f c : ℕ → ℝ)
    (hf : ∀ n, 0 ≤ f n) (hc : ∀ n, 0 ≤ c n)
    (hrec : ∀ n, f (n + 1) = c n * f n)
    (hlim : Tendsto c atTop (𝓝 0)) (j : ℕ) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ j * f n) := by
  have hpos (n : ℕ) : 0 ≤ ((n : ℝ) + 1) ^ j * f n :=
    mul_nonneg (pow_nonneg (by positivity) j) (hf n)
  have hlim' : Tendsto (fun n => (2 : ℝ) ^ j * c n) atTop (𝓝 0) := by
    simpa using hlim.const_mul ((2 : ℝ) ^ j)
  apply summable_of_ratio_norm_eventually_le (r := (1 / 2 : ℝ)) (by norm_num)
  filter_upwards [hlim'.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2)] with n hn
  rw [Real.norm_of_nonneg (hpos (n + 1)), Real.norm_of_nonneg (hpos n), hrec]
  push_cast
  have hp : ((n : ℝ) + 1 + 1) ^ j ≤ (2 : ℝ) ^ j * ((n : ℝ) + 1) ^ j := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by nlinarith [Nat.cast_nonneg (α := ℝ) n]) j
  calc
    ((n : ℝ) + 1 + 1) ^ j * (c n * f n) ≤
        (2 ^ j * ((n : ℝ) + 1) ^ j) * (c n * f n) :=
      mul_le_mul_of_nonneg_right hp (mul_nonneg (hc n) (hf n))
    _ = (2 ^ j * c n) * (((n : ℝ) + 1) ^ j * f n) := by ring
    _ ≤ 1 / 2 * (((n : ℝ) + 1) ^ j * f n) :=
      mul_le_mul_of_nonneg_right hn (hpos n)

theorem tendsto_linear_times_q_four (L d q : ℝ) (hq : 0 ≤ q) (hq1 : q < 1) :
    Tendsto (fun n : ℕ => L * (2 * (n : ℝ) + d) * q ^ (4 * n)) atTop (𝓝 0) := by
  have h4 : q ^ 4 < 1 := pow_lt_one₀ hq hq1 (by decide)
  have h0 := tendsto_pow_const_mul_const_pow_of_lt_one 0 (pow_nonneg hq 4) h4
  have h1 := tendsto_pow_const_mul_const_pow_of_lt_one 1 (pow_nonneg hq 4) h4
  simp only [pow_zero, one_mul] at h0
  simp only [pow_one] at h1
  have ht := (h1.const_mul (2 : ℝ)).add (h0.const_mul d)
  have ht' : Tendsto (fun n : ℕ => (2 * (n : ℝ) + d) * (q ^ 4) ^ n) atTop (𝓝 0) := by
    convert ht using 1
    · funext n
      ring
    · simp
  simpa only [pow_mul, mul_zero, mul_assoc] using ht'.const_mul L

theorem summable_evenMatchedBound_polynomial {A C q : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hq : 0 ≤ q) (hq1 : q < 1) (j : ℕ) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ j * evenMatchedBound A C q n) := by
  apply summable_polynomial_of_nonnegative_recurrence _
    (fun n => A ^ 2 * C * (2 * (n : ℝ) + 1) * q ^ (4 * n))
  · intro n
    unfold evenMatchedBound
    positivity
  · intro n
    positivity
  · exact evenMatchedBound_succ A C q
  · exact tendsto_linear_times_q_four (A ^ 2 * C) 1 q hq hq1

theorem summable_oddMatchedBound_polynomial {A C q : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hq : 0 ≤ q) (hq1 : q < 1) (j : ℕ) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ j * oddMatchedBound A C q n) := by
  apply summable_polynomial_of_nonnegative_recurrence _
    (fun n => A ^ 2 * C * (2 * (n : ℝ) + 3) * q ^ (4 * n + 2))
  · intro n
    unfold oddMatchedBound
    positivity
  · intro n
    positivity
  · exact oddMatchedBound_succ A C q
  · have ht := tendsto_linear_times_q_four (A ^ 2 * C) 3 q hq hq1
    simpa only [pow_add, ← mul_assoc, zero_mul] using ht.mul_const (q ^ 2)

theorem retained_even_bound_rearrange (A C D q : ℝ) (m n : ℕ) :
    A ^ (m + 2 * n) * (D ^ m.choose 2 * C ^ (m * (2 * n)) *
      ((matchingNumber n : ℝ) * C ^ n * q ^ (2 * n * (n - 1)))) =
      (A ^ m * D ^ m.choose 2) * evenMatchedBound (A * C ^ m) C q n := by
  simp only [evenMatchedBound, mul_pow, pow_add, ← pow_mul]
  ring

theorem retained_odd_bound_rearrange (A C D q : ℝ) (m n : ℕ) :
    A ^ (m + (2 * n + 1)) * (D ^ m.choose 2 * C ^ (m * (2 * n + 1)) *
      ((matchingNumber (n + 1) : ℝ) * C ^ n * q ^ (2 * n * n))) =
      (A ^ m * D ^ m.choose 2) * oddMatchedBound (A * C ^ m) C q n := by
  simp only [oddMatchedBound, mul_pow, pow_add, ← pow_mul]
  ring

theorem summable_retained_even_bound {A C D q : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hq : 0 ≤ q) (hq1 : q < 1) (m j : ℕ) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ j *
      (A ^ (m + 2 * n) * (D ^ m.choose 2 * C ^ (m * (2 * n)) *
        ((matchingNumber n : ℝ) * C ^ n * q ^ (2 * n * (n - 1)))))) := by
  simp_rw [retained_even_bound_rearrange]
  have hs := (summable_evenMatchedBound_polynomial
    (mul_nonneg hA (pow_nonneg hC m)) hC hq hq1 j).mul_left (A ^ m * D ^ m.choose 2)
  convert hs using 1
  funext n
  ring

theorem summable_retained_odd_bound {A C D q : ℝ}
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hq : 0 ≤ q) (hq1 : q < 1) (m j : ℕ) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ j *
      (A ^ (m + (2 * n + 1)) * (D ^ m.choose 2 * C ^ (m * (2 * n + 1)) *
        ((matchingNumber (n + 1) : ℝ) * C ^ n * q ^ (2 * n * n))))) := by
  simp_rw [retained_odd_bound_rearrange]
  have hs := (summable_oddMatchedBound_polynomial
    (mul_nonneg hA (pow_nonneg hC m)) hC hq hq1 j).mul_left (A ^ m * D ^ m.choose 2)
  convert hs using 1
  funext n
  ring

end
end IsingBulk.AnisoF002.RegularTail.C03
