import IsingBulk.AnisoF002.C03.NegativeGaussianMarginalDensity
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The actual Gaussian coordinate-tail density estimate

The complete marginal normalization and insertion expectation are retained.
The elementary factorial bound comes from one nonnegative exponential-series
term.  A positive fourth-degree Taylor polynomial proves the printed
threshold `x^2 >= 16 n` without assuming a logarithmic estimate.
-/

namespace IsingBulk.AnisoF002.NegativeHT.Angular
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem marginalScale_le_two (d : ℕ) : marginalScale d ≤ 2 := by
  rw [marginalScale, div_le_iff₀ (by positivity)]
  push_cast
  linarith [Nat.cast_nonneg (α := ℝ) d]

theorem constrained_gaussian_marginal_ratio_le (d : ℕ) :
    constrainedGaussianIntegral d / constrainedGaussianIntegral (d + 1) ≤
      (2 : ℝ) ^ (d + 2) / ((d + 2).factorial : ℝ) := by
  rw [constrained_gaussian_marginal_ratio]
  have hs : Real.sqrt (marginalScale d) ≤ 2 := by
    have hsq := Real.sq_sqrt (marginalScale_pos d).le
    nlinarith [Real.sqrt_nonneg (marginalScale d), marginalScale_le_two d]
  have hp : 1 ≤ Real.sqrt Real.pi := by
    have hsq := Real.sq_sqrt Real.pi_pos.le
    nlinarith [Real.sqrt_nonneg Real.pi, Real.two_le_pi]
  change (2 : ℝ) ^ (d + 1) / (Real.sqrt Real.pi * ((d + 2).factorial : ℝ)) *
    Real.sqrt (marginalScale d) ≤ _
  calc
    _ ≤ ((2 : ℝ) ^ (d + 1) / ((d + 2).factorial : ℝ)) * 2 := by
      apply mul_le_mul _ hs (Real.sqrt_nonneg _) (by positivity)
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith [Nat.cast_nonneg (α := ℝ) ((d + 2).factorial)]
    _ = _ := by rw [show d + 2 = d + 1 + 1 by omega, pow_succ]; ring

theorem gaussianMarginalDensity_le_polynomial {d : ℕ} (hd : 0 < d) (x : ℝ) :
    gaussianMarginalDensity d x ≤
      ((2 : ℝ) ^ (d + 2) / ((d + 2).factorial : ℝ)) * Real.exp (-x ^ 2) *
        (3 * x ^ 2 + ((d + 2 : ℕ) : ℝ)) ^ (d + 1) := by
  unfold gaussianMarginalDensity
  apply mul_le_mul _ (marginal_insertion_expectation_le hd x)
    (integral_nonneg (fun _ => Finset.prod_nonneg (fun _ _ => sq_nonneg _))) (by positivity)
  apply mul_le_mul (constrained_gaussian_marginal_ratio_le d) _
    (Real.exp_nonneg _) (by positivity)
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr (marginalScale_one_le d)) (sq_nonneg x)]

theorem gaussianMarginalDensity_le_scaled {d : ℕ} (hd : 0 < d) (x : ℝ) :
    gaussianMarginalDensity d x ≤
      (1 / ((d + 2 : ℕ) : ℝ)) * (2 * Real.exp 1) ^ (d + 2) *
        (1 + 3 * (x ^ 2 / ((d + 2 : ℕ) : ℝ))) ^ (d + 1) * Real.exp (-x ^ 2) := by
  let n : ℝ := ((d + 2 : ℕ) : ℝ)
  have hn : 0 < n := by dsimp [n]; positivity
  have hfactor : n ^ (d + 2) / ((d + 2).factorial : ℝ) ≤ Real.exp n :=
    Real.pow_div_factorial_le_exp n hn.le (d + 2)
  have hpoly : 3 * x ^ 2 + n = n * (1 + 3 * (x ^ 2 / n)) := by
    field_simp
    ring
  have hstep : ((2 : ℝ) ^ (d + 2) / ((d + 2).factorial : ℝ)) * Real.exp (-x ^ 2) *
      (3 * x ^ 2 + n) ^ (d + 1) =
      (1 / n) * ((2 : ℝ) ^ (d + 2) * (n ^ (d + 2) / ((d + 2).factorial : ℝ))) *
        (1 + 3 * (x ^ 2 / n)) ^ (d + 1) * Real.exp (-x ^ 2) := by
    rw [hpoly, mul_pow, show d + 2 = d + 1 + 1 by omega]
    rw [pow_succ n]
    field_simp
    ring
  calc
    gaussianMarginalDensity d x ≤ _ := gaussianMarginalDensity_le_polynomial hd x
    _ = _ := hstep
    _ ≤ (1 / n) * ((2 : ℝ) ^ (d + 2) * Real.exp n) *
        (1 + 3 * (x ^ 2 / n)) ^ (d + 1) * Real.exp (-x ^ 2) := by
      gcongr
    _ = _ := by
      have he : Real.exp n = Real.exp 1 ^ (d + 2) := by
        simpa only [mul_one, n] using Real.exp_nat_mul 1 (d + 2)
      rw [he, ← mul_pow]

theorem two_exp_one_mul_linear_le_exp {t : ℝ} (ht : 16 ≤ t) :
    2 * Real.exp 1 * (1 + 3 * t) ≤ Real.exp (t / 2) := by
  have ht0 : 0 ≤ t := by linarith
  have hu : 0 ≤ t - 16 := by linarith
  have hpoly : 0 ≤ 3 + (271 / 6 : ℝ) * (t - 16) +
      (41 / 8 : ℝ) * (t - 16) ^ 2 + (3 / 16 : ℝ) * (t - 16) ^ 3 +
        (1 / 384 : ℝ) * (t - 16) ^ 4 := by positivity
  have hexp := Real.sum_le_exp_of_nonneg (show 0 ≤ t / 2 by positivity) 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at hexp
  have hsmall : 2 * Real.exp 1 * (1 + 3 * t) ≤ 6 * (1 + 3 * t) := by
    have h := mul_nonneg (show 0 ≤ 3 - Real.exp 1 by linarith [Real.exp_one_lt_three])
      (show 0 ≤ 1 + 3 * t by positivity)
    nlinarith
  apply hsmall.trans
  nlinarith

/-- The printed complete marginal tail bound, for every particle number `n >= 3`. -/
theorem gaussianMarginalDensity_tail {d : ℕ} (hd : 0 < d) (x : ℝ)
    (hx : 16 * ((d + 2 : ℕ) : ℝ) ≤ x ^ 2) :
    gaussianMarginalDensity d x ≤
      (1 / ((d + 2 : ℕ) : ℝ)) * Real.exp (-x ^ 2 / 2) := by
  let n : ℝ := ((d + 2 : ℕ) : ℝ)
  let t : ℝ := x ^ 2 / n
  have hn : 0 < n := by dsimp [n]; positivity
  have ht : 16 ≤ t := (le_div_iff₀ hn).mpr hx
  have hb : 1 ≤ 1 + 3 * t := by linarith
  have hp : (2 * Real.exp 1) ^ (d + 2) * (1 + 3 * t) ^ (d + 1) ≤
      Real.exp (x ^ 2 / 2) := by
    calc
      _ ≤ (2 * Real.exp 1) ^ (d + 2) * (1 + 3 * t) ^ (d + 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_right₀ hb (by omega)
      _ = (2 * Real.exp 1 * (1 + 3 * t)) ^ (d + 2) := (mul_pow _ _ _).symm
      _ ≤ Real.exp (t / 2) ^ (d + 2) :=
        pow_le_pow_left₀ (by positivity) (two_exp_one_mul_linear_le_exp ht) _
      _ = _ := by
        rw [← Real.exp_nat_mul]
        congr 1
        change n * ((x ^ 2 / n) / 2) = x ^ 2 / 2
        field_simp
  calc
    gaussianMarginalDensity d x ≤ _ := gaussianMarginalDensity_le_scaled hd x
    _ = (1 / n) * ((2 * Real.exp 1) ^ (d + 2) * (1 + 3 * t) ^ (d + 1)) *
        Real.exp (-x ^ 2) := by dsimp [n, t]; ring
    _ ≤ (1 / n) * Real.exp (x ^ 2 / 2) * Real.exp (-x ^ 2) := by
      gcongr
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

end
end IsingBulk.AnisoF002.NegativeHT.Angular
