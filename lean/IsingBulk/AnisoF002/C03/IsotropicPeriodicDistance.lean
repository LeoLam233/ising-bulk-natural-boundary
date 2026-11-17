import IsingBulk.AnisoF002.C03.IsotropicFrozenProjection
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The exact periodic distance in the oblique kernel estimate

The norm on the additive circle is identified with metric distance to
the integer period lattice. A quantitative exponential chord estimate
is proved using the actual nearest winding and Jordan's inequality.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology
open Set Metric

def periodicDistance (p x : ℝ) : ℝ := ‖(x : AddCircle p)‖

theorem periodicDistance_eq_infDist (p x : ℝ) :
    periodicDistance p x = infDist x (AddSubgroup.zmultiples p : Set ℝ) := by
  exact QuotientAddGroup.norm_mk x

theorem periodicDistance_nonneg (p x : ℝ) : 0 ≤ periodicDistance p x := norm_nonneg _

theorem periodicDistance_le_abs (p x : ℝ) : periodicDistance p x ≤ |x| := by
  exact (QuotientAddGroup.norm_mk_le_norm (m := x)).trans_eq (Real.norm_eq_abs x)

theorem periodicDistance_le_half (p x : ℝ) (hp : 0 < p) : periodicDistance p x ≤ p / 2 := by
  simpa only [periodicDistance, abs_of_pos hp] using AddCircle.norm_le_half_period p hp.ne' (x := (x : AddCircle p))

theorem periodicDistance_scaled (p x a : ℝ) :
    periodicDistance (a * p) (a * x) = |a| * periodicDistance p x :=
  AddCircle.norm_coe_mul p x a

theorem periodicDistance_sub_le (p x y : ℝ) :
    periodicDistance p (x - y) ≤ periodicDistance p x + |y| := by
  unfold periodicDistance
  rw [AddCircle.coe_sub]
  exact (norm_sub_le _ _).trans (add_le_add le_rfl (periodicDistance_le_abs p y))

theorem periodicDistance_periodic (p : ℝ) : Function.Periodic (periodicDistance p) p := by
  intro x
  simp only [periodicDistance, AddCircle.coe_add_period]

theorem complex_exp_neg_angle_winding (x : ℝ) (n : ℤ) :
    Complex.exp (-Complex.I * ((x - (n : ℝ) * (2 * Real.pi) : ℝ) : ℂ)) =
      Complex.exp (-Complex.I * (x : ℂ)) := by
  have he : -Complex.I * ((x - (n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) =
      -Complex.I * (x : ℂ) + (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [he, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem periodicDistance_exp_chord (x : ℝ) :
    periodicDistance (2 * Real.pi) x ≤
      (Real.pi / 2) * ‖1 - Complex.exp (-Complex.I * (x : ℂ))‖ := by
  let n : ℤ := round ((2 * Real.pi)⁻¹ * x)
  let y := x - (n : ℝ) * (2 * Real.pi)
  have hd : periodicDistance (2 * Real.pi) x = |y| := AddCircle.norm_eq (2 * Real.pi)
  have hy : |y| ≤ Real.pi := by
    have hh := periodicDistance_le_half (2 * Real.pi) x (by positivity)
    rw [hd] at hh
    linarith only [hh]
  have hj := Real.mul_abs_le_abs_sin (x := y / 2) (by rw [abs_div, abs_two]; linarith only [hy])
  have hn : ‖1 - Complex.exp (-Complex.I * (y : ℂ))‖ = 2 * |Real.sin (y / 2)| := by
    rw [norm_sub_rev, show -Complex.I * (y : ℂ) = Complex.I * ((-y : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_exp_I_mul_ofReal_sub_one]
    simp only [Real.norm_eq_abs, abs_mul, abs_two, neg_div, Real.sin_neg, abs_neg]
  rw [← complex_exp_neg_angle_winding x n, hd]
  change |y| ≤ (Real.pi / 2) * ‖1 - Complex.exp (-Complex.I * (y : ℂ))‖
  rw [hn]
  rw [abs_div, abs_two] at hj
  have hh := mul_le_mul_of_nonneg_left hj Real.pi_pos.le
  field_simp at hh
  nlinarith only [hh]

end IsingBulk.AnisoF002.Isotropic
