import IsingBulk.AnisoF002.RegularTail.GaussianEnvelope
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# All-order Gaussian coefficient sums

The complete analytic remainder on disks of radius c/N has coefficients
bounded by (CN)^j times a Gaussian in N.  This file proves the uniform
half-order logarithmic growth estimate for that entire infinite sum.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Filter IsingBulk.AnisoF002.RegularTail
open scoped BigOperators

theorem gaussian_moment_pointwise (j : ℕ) {κ x : ℝ} (hκ : 0 < κ) (hx : 0 ≤ x) :
    x ^ j * Real.exp (-κ * x ^ 2) ≤
      Real.exp ((j : ℝ) / 2 * Real.log ((j + 1 : ℕ) : ℝ) -
        (j : ℝ) / 2 * Real.log κ) * Real.exp (-(κ / 2) * x ^ 2) := by
  by_cases hx0 : x = 0
  · subst x
    by_cases hj : j = 0
    · subst j; norm_num
    · simp only [zero_pow hj, zero_mul]
      positivity
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hJ : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
  have hy : 0 < κ * x ^ 2 / ((j + 1 : ℕ) : ℝ) := by positivity
  have hlog := Real.log_le_sub_one_of_pos hy
  rw [Real.log_div (by positivity) hJ.ne', Real.log_mul hκ.ne'
    (pow_ne_zero _ hx0), Real.log_pow] at hlog
  have hm := mul_le_mul_of_nonneg_left hlog (show 0 ≤ (j : ℝ) / 2 by positivity)
  have hquad : (j : ℝ) * (κ * x ^ 2 / ((j + 1 : ℕ) : ℝ)) ≤ κ * x ^ 2 := by
    calc
      _ ≤ ((j + 1 : ℕ) : ℝ) * (κ * x ^ 2 / ((j + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right (by push_cast; linarith) hy.le
      _ = _ := mul_div_cancel₀ _ hJ.ne'
  have hexp : (j : ℝ) * Real.log x - κ * x ^ 2 ≤
      (j : ℝ) / 2 * Real.log ((j + 1 : ℕ) : ℝ) -
        (j : ℝ) / 2 * Real.log κ - (κ / 2) * x ^ 2 := by nlinarith
  have hxpow : x ^ j = Real.exp ((j : ℝ) * Real.log x) := by
    rw [Real.exp_nat_mul, Real.exp_log hxpos]
  rw [hxpow, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simpa only [sub_eq_add_neg, neg_mul] using hexp

theorem gaussian_moment_sum_bound (j : ℕ) {κ : ℝ} (hκ : 0 < κ) :
    Summable (fun n : ℕ => (n : ℝ) ^ j * Real.exp (-κ * (n : ℝ) ^ 2)) ∧
      (∑' n : ℕ, (n : ℝ) ^ j * Real.exp (-κ * (n : ℝ) ^ 2)) ≤
        Real.exp ((j : ℝ) / 2 * Real.log ((j + 1 : ℕ) : ℝ) -
          (j : ℝ) / 2 * Real.log κ) *
          ∑' n : ℕ, Real.exp (-(κ / 2) * (n : ℝ) ^ 2) := by
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ j * Real.exp (-κ * (n : ℝ) ^ 2)) := by
    simpa only [zero_mul, add_zero] using gaussian_log_envelope_summable j hκ
      (show (0 : ℝ) ≤ 0 by rfl)
  have hgauss : Summable (fun n : ℕ => Real.exp (-(κ / 2) * (n : ℝ) ^ 2)) := by
    simpa only [zero_mul, add_zero, pow_zero, one_mul] using
      gaussian_log_envelope_summable 0 (half_pos hκ) (show (0 : ℝ) ≤ 0 by rfl)
  refine ⟨hsum, ?_⟩
  rw [← tsum_mul_left]
  exact hsum.tsum_le_tsum (fun n => gaussian_moment_pointwise j hκ (Nat.cast_nonneg n))
    (hgauss.mul_left _)

theorem exists_scaled_gaussian_moment_bound {κ C : ℝ} (hκ : 0 < κ) (hC : 0 < C) :
    ∃ A : ℝ, 0 < A ∧ ∀ j : ℕ,
      Summable (fun n : ℕ => (C * (n : ℝ)) ^ j * Real.exp (-κ * (n : ℝ) ^ 2)) ∧
      (∑' n : ℕ, (C * (n : ℝ)) ^ j * Real.exp (-κ * (n : ℝ) ^ 2)) ≤
        Real.exp ((j : ℝ) / 2 * Real.log ((j + 1 : ℕ) : ℝ) + A * (j : ℝ) + A) := by
  let S : ℝ := ∑' n : ℕ, Real.exp (-(κ / 2) * (n : ℝ) ^ 2)
  let A : ℝ := 1 + |Real.log C| + |Real.log κ| / 2 + |Real.log (S + 1)|
  have hS : 0 ≤ S := tsum_nonneg (fun n => (Real.exp_pos _).le)
  have hA : 0 < A := by dsimp [A]; positivity
  have hSA : S ≤ Real.exp A := by
    apply le_trans (by linarith : S ≤ S + 1)
    apply (Real.log_le_iff_le_exp (by linarith : 0 < S + 1)).mp
    have hh := le_abs_self (Real.log (S + 1))
    dsimp [A]
    linarith [abs_nonneg (Real.log C), abs_nonneg (Real.log κ)]
  refine ⟨A, hA, ?_⟩
  intro j
  obtain ⟨hsum, hb⟩ := gaussian_moment_sum_bound j hκ
  have hfun : (fun n : ℕ => (C * (n : ℝ)) ^ j * Real.exp (-κ * (n : ℝ) ^ 2)) =
      (fun n : ℕ => C ^ j * ((n : ℝ) ^ j * Real.exp (-κ * (n : ℝ) ^ 2))) := by
    funext n
    rw [mul_pow, mul_assoc]
  rw [hfun]
  refine ⟨hsum.mul_left _, ?_⟩
  rw [tsum_mul_left]
  have hmain := mul_le_mul_of_nonneg_left hb (pow_nonneg hC.le j)
  have hcoef : (j : ℝ) * Real.log C - (j : ℝ) / 2 * Real.log κ ≤ A * (j : ℝ) := by
    have hc := le_abs_self (Real.log C)
    have hk := neg_le_abs (Real.log κ)
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have ha : Real.log C - Real.log κ / 2 ≤ A := by
      dsimp [A]
      linarith [abs_nonneg (Real.log (S + 1))]
    nlinarith
  calc
    _ ≤ C ^ j * (Real.exp ((j : ℝ) / 2 * Real.log ((j + 1 : ℕ) : ℝ) -
        (j : ℝ) / 2 * Real.log κ) * S) := hmain
    _ ≤ C ^ j * (Real.exp ((j : ℝ) / 2 * Real.log ((j + 1 : ℕ) : ℝ) -
        (j : ℝ) / 2 * Real.log κ) * Real.exp A) := by gcongr
    _ = Real.exp ((j : ℝ) * Real.log C +
        ((j : ℝ) / 2 * Real.log ((j + 1 : ℕ) : ℝ) - (j : ℝ) / 2 * Real.log κ) + A) := by
      conv_rhs => rw [Real.exp_add, Real.exp_add, Real.exp_nat_mul, Real.exp_log hC]
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end
end IsingBulk.AnisoF002.NegativeHT
