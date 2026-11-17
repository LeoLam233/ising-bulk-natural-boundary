import IsingBulk.AnisoF002.C03.NegativeVandermondeBallBound
import IsingBulk.AnisoF002.NegativeHT.FactorialRectangle

/-!
# The full high-particle collision mass scale

The actual complete Vandermonde ball integral has the leading
`-N² log N / 2` exponent.  This estimate holds before any Taylor order
is selected and includes the whole independent-coordinate ball.
-/

namespace IsingBulk.AnisoF002.NegativeHT.Angular
noncomputable section
open MeasureTheory Set

set_option maxHeartbeats 800000 in
theorem vandermonde_unit_bound_exponential {d : ℕ} (hd : 0 < d) :
    (2 : ℝ) ^ d * (8 / (d : ℝ)) ^ (d + 1).choose 2 ≤
      Real.exp (-(((d + 1 : ℕ) : ℝ)) ^ 2 / 2 * Real.log ((d + 1 : ℕ) : ℝ) +
        4 * (((d + 1 : ℕ) : ℝ)) ^ 2) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hn0 : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by positivity
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hq : (((d + 1).choose 2 : ℕ) : ℝ) = ((d + 1 : ℕ) : ℝ) * (d : ℝ) / 2 := by
    rw [Nat.cast_choose_two]
    push_cast
    ring
  have hl2 : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hl8 : Real.log 8 ≤ 3 := by
    have hh := Real.log_pow (2 : ℝ) 3
    norm_num at hh
    linarith
  have hlN : Real.log ((d + 1 : ℕ) : ℝ) ≤ (d : ℝ) := by
    have hh := Real.log_le_sub_one_of_pos hn0
    push_cast at hh ⊢
    linarith
  have hstep := (log_increment_bounds hd0 (by norm_num : (0 : ℝ) ≤ 1)).2
  have hstep' : (d : ℝ) * (Real.log ((d + 1 : ℕ) : ℝ) - Real.log (d : ℝ)) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hstep hd0.le
    have hi : (d : ℝ) * (1 / (d : ℝ)) = 1 := by field_simp
    rw [hi] at hh
    simpa only [Nat.cast_add, Nat.cast_one] using hh
  have hdeficit : (((d + 1 : ℕ) : ℝ)) ^ 2 / 2 * Real.log ((d + 1 : ℕ) : ℝ) -
      (((d + 1).choose 2 : ℕ) : ℝ) * Real.log (d : ℝ) ≤
        (((d + 1 : ℕ) : ℝ)) ^ 2 / 2 := by
    have hh := mul_le_mul_of_nonneg_left (add_le_add hstep' hlN) (half_pos hn0).le
    rw [hq]
    push_cast at *
    nlinarith
  have hsmall : (d : ℝ) * Real.log 2 +
      (((d + 1).choose 2 : ℕ) : ℝ) * Real.log 8 ≤
        3 * (((d + 1 : ℕ) : ℝ)) ^ 2 := by
    have ha := mul_le_mul_of_nonneg_left hl2 hd0.le
    have hb := mul_le_mul_of_nonneg_left hl8 (Nat.cast_nonneg ((d + 1).choose 2))
    rw [hq] at hb ⊢
    push_cast at *
    nlinarith
  have hpos : 0 < (2 : ℝ) ^ d * (8 / (d : ℝ)) ^ (d + 1).choose 2 := by positivity
  apply (Real.log_le_iff_le_exp hpos).mp
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    Real.log_div (by norm_num) hd0.ne']
  nlinarith

theorem full_vandermonde_ball_exponential_bound {d : ℕ} (hd : 0 < d)
    {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) :
    (∫ v in Metric.closedBall (0 : constrainedPlane d) R,
      planeVandermonde v ∂independentMeasure d) ≤
      Real.exp (-(((d + 1 : ℕ) : ℝ)) ^ 2 / 2 * Real.log ((d + 1 : ℕ) : ℝ) +
        4 * (((d + 1 : ℕ) : ℝ)) ^ 2) := by
  apply (full_vandermonde_ball_integral_bound hd hR).trans
  apply le_trans _ (vandermonde_unit_bound_exponential hd)
  apply mul_le_mul
  · exact pow_le_pow_left₀ (by positivity) (by linarith : 2 * R ≤ (2 : ℝ)) d
  · apply pow_le_pow_left₀ (by positivity)
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg d)
    nlinarith
  · positivity
  · positivity

end
end IsingBulk.AnisoF002.NegativeHT.Angular
