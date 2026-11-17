import IsingBulk.AnisoF002.C03.RegularMatching
import IsingBulk.AnisoF002.C03.PhysicalHadamardSummability

/-!
# Complete matching/factorial envelopes for the mixed isotropic tail

The literal all-matching count from the physical Pfaffian numerator is
kept together with the original N! normalization. Every fixed polynomial
loss in N and every finite exponential constant are summable over the
complete particle sequence and either parity.
-/

noncomputable section
namespace IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators

theorem matchingNumber_le_power (k N : ℕ) (h : 2 * k ≤ N + 1) :
    matchingNumber k ≤ N ^ k := by
  induction k with
  | zero => simp only [matchingNumber, pow_zero, le_refl]
  | succ k ih =>
    rw [matchingNumber, pow_succ']
    exact Nat.mul_le_mul (by omega) (ih (by omega))

theorem matchingNumber_particle_bound (N : ℕ) :
    (matchingNumber ((N + 1) / 2) : ℝ) ≤ (N : ℝ) ^ (N - N / 2) := by
  have he : (N + 1) / 2 = N - N / 2 := by omega
  have hh := matchingNumber_le_power ((N + 1) / 2) N (by omega)
  rw [he] at hh ⊢
  exact_mod_cast hh

def mixedFactorialEnvelope (A : ℝ) (j N : ℕ) : ℝ :=
  (N : ℝ) ^ j * A ^ N * (matchingNumber ((N + 1) / 2) : ℝ) / (N.factorial : ℝ)

theorem mixedFactorialEnvelope_le_hadamard {A : ℝ} (hA : 0 ≤ A) (j N : ℕ) :
    mixedFactorialEnvelope A j N ≤ literalHadamardEnvelope (A * 2 ^ j) N := by
  have hN : (N : ℝ) ≤ (2 : ℝ) ^ N := by exact_mod_cast (Nat.lt_two_pow_self (n := N)).le
  have hp : (N : ℝ) ^ j ≤ ((2 : ℝ) ^ j) ^ N := by
    calc
      _ ≤ ((2 : ℝ) ^ N) ^ j := pow_le_pow_left₀ (Nat.cast_nonneg _) hN j
      _ = _ := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have hnum := mul_le_mul
    (mul_le_mul_of_nonneg_right hp (pow_nonneg hA N))
    (matchingNumber_particle_bound N) (Nat.cast_nonneg _) (by positivity)
  have hh := div_le_div_of_nonneg_right hnum (show (0 : ℝ) ≤ N.factorial by positivity)
  calc
    _ ≤ ((2 : ℝ) ^ j) ^ N * A ^ N * (N : ℝ) ^ (N - N / 2) / (N.factorial : ℝ) := hh
    _ = _ := by unfold literalHadamardEnvelope; rw [mul_pow]; ring

theorem mixedFactorialEnvelope_summable {A : ℝ} (hA : 0 ≤ A) (j : ℕ) :
    Summable (mixedFactorialEnvelope A j) :=
  (literalHadamardEnvelope_summable (mul_nonneg hA (by positivity))).of_nonneg_of_le
    (fun N => by unfold mixedFactorialEnvelope; positivity) (mixedFactorialEnvelope_le_hadamard hA j)

theorem mixedFactorialEnvelope_even_summable {A : ℝ} (hA : 0 ≤ A) (j : ℕ) :
    Summable (fun n => mixedFactorialEnvelope A j (2 * n)) :=
  (mixedFactorialEnvelope_summable hA j).comp_injective (by intro m n h; omega)

theorem mixedFactorialEnvelope_odd_summable {A : ℝ} (hA : 0 ≤ A) (j : ℕ) :
    Summable (fun n => mixedFactorialEnvelope A j (2 * n + 1)) :=
  (mixedFactorialEnvelope_summable hA j).comp_injective (by intro m n h; dsimp at h; omega)

end IsingBulk.AnisoF002.RegularTail.C03
