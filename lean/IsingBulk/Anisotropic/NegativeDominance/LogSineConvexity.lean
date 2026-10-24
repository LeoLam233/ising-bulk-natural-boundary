import IsingBulk.Anisotropic.NegativeDominance.LogSineBounds
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Convexity of the exact resonance logarithm on the large-particle range.
This controls its j-amplified term without differentiating a big-O error. -/
namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Set

def logSineReciprocal (c x : ℝ) : ℝ := Real.log (Real.sin (c / x))
def logSineReciprocalD (c x : ℝ) : ℝ :=
  -c * Real.cos (c / x) / (x^2 * Real.sin (c / x))
def logSineReciprocalDD (c x : ℝ) : ℝ :=
  (2 * c * x * Real.sin (c / x) * Real.cos (c / x) - c^2) /
    (x^4 * Real.sin (c / x)^2)

theorem hasDerivAt_logSineReciprocal (c x : ℝ) (hx : x ≠ 0)
    (hs : Real.sin (c / x) ≠ 0) :
    HasDerivAt (logSineReciprocal c) (logSineReciprocalD c x) x := by
  have ha := (hasDerivAt_const x c).div (hasDerivAt_id x) hx
  have hsin := (Real.hasDerivAt_sin (c / x)).comp x ha
  have hh := (Real.hasDerivAt_log hs).comp x hsin
  convert hh using 1
  · rfl
  · dsimp [logSineReciprocalD]
    field_simp
    ring

theorem hasDerivAt_logSineReciprocalD (c x : ℝ) (hx : x ≠ 0)
    (hs : Real.sin (c / x) ≠ 0) :
    HasDerivAt (logSineReciprocalD c) (logSineReciprocalDD c x) x := by
  have ha := (hasDerivAt_const x c).div (hasDerivAt_id x) hx
  have hsin := (Real.hasDerivAt_sin (c / x)).comp x ha
  have hcos := (Real.hasDerivAt_cos (c / x)).comp x ha
  have hh := (hcos.const_mul (-c)).div (((hasDerivAt_id x).pow 2).mul hsin)
    (mul_ne_zero (pow_ne_zero _ hx) hs)
  convert hh using 1
  · rfl
  · dsimp [logSineReciprocalDD]
    field_simp
    have hid := Real.sin_sq_add_cos_sq (c / x)
    nlinarith [sq_nonneg c]

theorem sin_pos_of_pos_le_half {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1 / 2) :
    0 < Real.sin u := by
  have hs := Real.sin_gt_sub_cube hu
  have hu2 : u^2 ≤ 1 / 4 := by nlinarith
  have hu3 := mul_le_mul_of_nonneg_left hu2 hu.le
  nlinarith

theorem sin_double_ge_self {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1 / 2) :
    u ≤ Real.sin (2 * u) := by
  have hs := Real.sin_ge_sub_cube (show 0 ≤ 2 * u by positivity)
  have hu2 : u^2 ≤ 1 / 4 := by nlinarith
  have hu3 := mul_le_mul_of_nonneg_left hu2 hu.le
  nlinarith

theorem logSineReciprocalDD_nonneg {c x : ℝ} (hc : 0 < c) (hx : 2 * c ≤ x) :
    0 ≤ logSineReciprocalDD c x := by
  have hxp : 0 < x := by linarith
  have hu : 0 < c / x := div_pos hc hxp
  have hu1 : c / x ≤ 1 / 2 := by apply (div_le_iff₀ hxp).mpr; linarith
  have hh := sin_double_ge_self hu hu1
  rw [Real.sin_two_mul] at hh
  have hn : c ≤ (2 * Real.sin (c / x) * Real.cos (c / x)) * x :=
    (div_le_iff₀ hxp).mp hh
  unfold logSineReciprocalDD
  apply div_nonneg
  · nlinarith [mul_nonneg hc.le (sub_nonneg.mpr hn)]
  · positivity

theorem convexOn_logSineReciprocal {c : ℝ} (hc : 0 < c) :
    ConvexOn ℝ (Ici (2 * c)) (logSineReciprocal c) := by
  have hs (x : ℝ) (hx : x ∈ Ici (2 * c)) : Real.sin (c / x) ≠ 0 := by
    have hxp : 0 < x := by have := hx; simp only [mem_Ici] at this; linarith
    exact (sin_pos_of_pos_le_half (div_pos hc hxp)
      ((div_le_iff₀ hxp).mpr (by have := hx; simp only [mem_Ici] at this; linarith))).ne'
  have hxne (x : ℝ) (hx : x ∈ Ici (2 * c)) : x ≠ 0 := by
    have := hx
    simp only [mem_Ici] at this
    linarith
  apply convexOn_of_hasDerivWithinAt2_nonneg (f' := logSineReciprocalD c)
    (f'' := logSineReciprocalDD c) (convex_Ici _)
  · intro x hx
    exact (hasDerivAt_logSineReciprocal c x (hxne x hx) (hs x hx)).continuousAt.continuousWithinAt
  · intro x hx
    exact (hasDerivAt_logSineReciprocal c x (hxne x (interior_subset hx))
      (hs x (interior_subset hx))).hasDerivWithinAt
  · intro x hx
    exact (hasDerivAt_logSineReciprocalD c x (hxne x (interior_subset hx))
      (hs x (interior_subset hx))).hasDerivWithinAt
  · intro x hx
    exact logSineReciprocalDD_nonneg hc (interior_subset hx)

end
end IsingBulk.Anisotropic.NegativeDominance
