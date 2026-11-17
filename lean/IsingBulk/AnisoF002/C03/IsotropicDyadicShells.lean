import IsingBulk.AnisoF002.C03.IsotropicBranchCoordinateScales
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Uniform dyadic summation at the actual frozen shell scale

The angular mean and positive radial depth are arbitrary and fixed.
One geometric ratio works at every scale and every positive collision
exponent. The largest-scale bound is uniform in both mean and depth.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric MeasureTheory

def shellDelta (μ ε r : ℝ) : ℝ := r / Real.sqrt (|μ| + r + ε)

theorem shellDelta_pos (μ ε r : ℝ) (hε : 0 < ε) (hr : 0 < r) : 0 < shellDelta μ ε r :=
  div_pos hr (Real.sqrt_pos.mpr (by positivity))

theorem shellDelta_half_bounds (μ ε r : ℝ) (hε : 0 < ε) (hr : 0 < r) :
    shellDelta μ ε r / 2 ≤ shellDelta μ ε (r / 2) ∧
      shellDelta μ ε (r / 2) ≤ (3 / 4 : ℝ) * shellDelta μ ε r := by
  have hT : 0 < |μ| + r + ε := by positivity
  have hH : 0 < |μ| + r / 2 + ε := by positivity
  have hTs : 0 < Real.sqrt (|μ| + r + ε) := Real.sqrt_pos.mpr hT
  have hHs : 0 < Real.sqrt (|μ| + r / 2 + ε) := Real.sqrt_pos.mpr hH
  have horder : Real.sqrt (|μ| + r / 2 + ε) ≤ Real.sqrt (|μ| + r + ε) :=
    Real.sqrt_le_sqrt (by linarith only [hr])
  have hsquare : Real.sqrt (|μ| + r + ε) ≤ (3 / 2 : ℝ) * Real.sqrt (|μ| + r / 2 + ε) := by
    have hsqT := Real.sq_sqrt hT.le
    have hsqH := Real.sq_sqrt hH.le
    nlinarith [abs_nonneg μ]
  constructor
  · change (r / Real.sqrt (|μ| + r + ε)) / 2 ≤ (r / 2) / Real.sqrt (|μ| + r / 2 + ε)
    rw [div_right_comm]
    exact div_le_div_of_nonneg_left (by positivity) hHs horder
  · change (r / 2) / Real.sqrt (|μ| + r / 2 + ε) ≤ (3 / 4 : ℝ) * (r / Real.sqrt (|μ| + r + ε))
    rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hHs hTs).mpr
    have hh := mul_le_mul_of_nonneg_left hsquare (show 0 ≤ r / 2 by positivity)
    nlinarith only [hh]

def dyadicRadius (r : ℝ) (k : ℕ) : ℝ := r / 2 ^ k

theorem dyadicRadius_pos (r : ℝ) (hr : 0 < r) (k : ℕ) : 0 < dyadicRadius r k := by
  dsimp [dyadicRadius]
  positivity

theorem dyadicRadius_zero (r : ℝ) : dyadicRadius r 0 = r := by simp [dyadicRadius]

theorem dyadicRadius_succ (r : ℝ) (k : ℕ) : dyadicRadius r (k + 1) = dyadicRadius r k / 2 := by
  rw [dyadicRadius, pow_succ, div_mul_eq_div_div]
  rfl

theorem shellDelta_dyadic_bound (μ ε r : ℝ) (hε : 0 < ε) (hr : 0 < r) (k : ℕ) :
    shellDelta μ ε (dyadicRadius r k) ≤ (3 / 4 : ℝ) ^ k * shellDelta μ ε r := by
  induction k with
  | zero => simp [dyadicRadius_zero]
  | succ k ih =>
    rw [dyadicRadius_succ]
    calc
      _ ≤ (3 / 4 : ℝ) * shellDelta μ ε (dyadicRadius r k) :=
        (shellDelta_half_bounds μ ε _ hε (dyadicRadius_pos r hr k)).2
      _ ≤ (3 / 4 : ℝ) * ((3 / 4 : ℝ) ^ k * shellDelta μ ε r) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = _ := by rw [pow_succ]; ring

theorem shellDelta_dyadic_power_bound (μ ε r : ℝ) (hε : 0 < ε) (hr : 0 < r) (n k : ℕ) :
    shellDelta μ ε (dyadicRadius r k) ^ (n + 1) ≤
      shellDelta μ ε r ^ (n + 1) * (3 / 4 : ℝ) ^ k := by
  have hq : 0 ≤ (3 / 4 : ℝ) ^ k := by positivity
  have hq1 : (3 / 4 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hp : ((3 / 4 : ℝ) ^ k) ^ (n + 1) ≤ (3 / 4 : ℝ) ^ k := by
    rw [pow_succ]
    exact mul_le_of_le_one_left hq (pow_le_one₀ hq hq1)
  calc
    _ ≤ ((3 / 4 : ℝ) ^ k * shellDelta μ ε r) ^ (n + 1) :=
      pow_le_pow_left₀ (shellDelta_pos μ ε _ hε (dyadicRadius_pos r hr k)).le
        (shellDelta_dyadic_bound μ ε r hε hr k) _
    _ = shellDelta μ ε r ^ (n + 1) * ((3 / 4 : ℝ) ^ k) ^ (n + 1) := by rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity [shellDelta_pos μ ε r hε hr])

/-- One geometric estimate sums every dyadic shell, uniformly in
mean, radial depth, and the positive retained collision exponent. -/
theorem shellDelta_dyadic_summable_bound (μ ε r : ℝ) (hε : 0 < ε) (hr : 0 < r) (n : ℕ) :
    Summable (fun k : ℕ => shellDelta μ ε (dyadicRadius r k) ^ (n + 1)) ∧
      (∑' k : ℕ, shellDelta μ ε (dyadicRadius r k) ^ (n + 1)) ≤ 4 * shellDelta μ ε r ^ (n + 1) := by
  have hgeo : HasSum (fun k : ℕ => shellDelta μ ε r ^ (n + 1) * (3 / 4 : ℝ) ^ k)
      (4 * shellDelta μ ε r ^ (n + 1)) := by
    convert (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 4)
      (by norm_num : (3 / 4 : ℝ) < 1)).mul_left (shellDelta μ ε r ^ (n + 1)) using 1
    ring
  have hs := hgeo.summable.of_nonneg_of_le
    (fun k => pow_nonneg (shellDelta_pos μ ε _ hε (dyadicRadius_pos r hr k)).le _)
    (shellDelta_dyadic_power_bound μ ε r hε hr n)
  exact ⟨hs, (hs.tsum_le_tsum (shellDelta_dyadic_power_bound μ ε r hε hr n) hgeo.summable).trans_eq hgeo.tsum_eq⟩

theorem shellDelta_le_sqrt_radius (μ ε r : ℝ) (hε : 0 < ε) (hr : 0 < r) :
    shellDelta μ ε r ≤ Real.sqrt r := by
  have hT : 0 < Real.sqrt (|μ| + r + ε) := Real.sqrt_pos.mpr (by positivity)
  apply (div_le_iff₀ hT).mpr
  have hh := mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (show r ≤ |μ| + r + ε by linarith only [abs_nonneg μ, hε])) (Real.sqrt_nonneg r)
  simpa only [← pow_two, Real.sq_sqrt hr.le] using hh

end IsingBulk.AnisoF002.Isotropic
