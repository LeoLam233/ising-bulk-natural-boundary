import IsingBulk.First.NormalizedContour
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! Exact normalized angle measures and the one-variable contour symmetries. -/
namespace IsingBulk.First
noncomputable section
open Complex MeasureTheory
open scoped BigOperators

def anglePoint (r θ : ℝ) : ℂ := circleMap 0 r θ

def angleJacobian (r θ : ℝ) : ℂ := anglePoint r θ / (2 * (Real.pi : ℂ))

theorem normalizedCircleIntegral_eq_angle (r : ℝ) (f : ℂ → ℂ) :
    normalizedCircleIntegral r f =
      ∫ θ : ℝ in 0..2*Real.pi, angleJacobian r θ * f (anglePoint r θ) := by
  unfold normalizedCircleIntegral circleIntegral
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [deriv_circleMap, smul_eq_mul, angleJacobian, anglePoint]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

theorem anglePoint_add_pi (r θ : ℝ) : anglePoint r (θ+Real.pi) = -anglePoint r θ := by
  simp [anglePoint, circleMap, add_mul, Complex.exp_add]

theorem anglePoint_conj (r θ : ℝ) : star (anglePoint r θ) = anglePoint r (-θ) := by
  exact conj_circleMap_zero r θ

theorem angleJacobian_conj (r θ : ℝ) : star (angleJacobian r θ) = angleJacobian r (-θ) := by
  unfold angleJacobian
  rw [star_div₀, anglePoint_conj]
  congr 1
  simp

theorem normalizedCircleIntegral_neg (r : ℝ) (f : ℂ → ℂ) :
    normalizedCircleIntegral r (fun z => f (-z)) = -normalizedCircleIntegral r f := by
  rw [normalizedCircleIntegral_eq_angle, normalizedCircleIntegral_eq_angle]
  let g : ℝ → ℂ := fun θ => angleJacobian r θ * f (anglePoint r θ)
  have hp : Function.Periodic g (2*Real.pi) := by
    intro θ
    simp only [g, angleJacobian, anglePoint, periodic_circleMap 0 r θ]
  have hs : (∫ θ : ℝ in 0..2*Real.pi, g (θ+Real.pi)) = ∫ θ : ℝ in 0..2*Real.pi, g θ := by
    rw [intervalIntegral.integral_comp_add_right]
    simpa [add_comm] using hp.intervalIntegral_add_eq Real.pi 0
  have hi : (fun θ : ℝ => angleJacobian r θ * f (-anglePoint r θ)) = fun θ => -g (θ+Real.pi) := by
    funext θ
    simp only [g, angleJacobian, anglePoint_add_pi, neg_div, neg_mul, neg_neg]
  rw [hi, intervalIntegral.integral_neg, hs]

theorem intervalIntegral_conjugate (f : ℝ → ℂ) (a b : ℝ) :
    (∫ θ in a..b, star (f θ)) = star (∫ θ in a..b, f θ) := by
  exact (RCLike.conjLIE.toLinearIsometry : ℂ →ₗᵢ[ℝ] ℂ).intervalIntegral_comp_comm f

theorem normalizedCircleIntegral_conjugate (r : ℝ) (f : ℂ → ℂ) :
    normalizedCircleIntegral r (fun z => star (f (star z))) = star (normalizedCircleIntegral r f) := by
  rw [normalizedCircleIntegral_eq_angle, normalizedCircleIntegral_eq_angle]
  let g : ℝ → ℂ := fun θ => star (angleJacobian r θ * f (anglePoint r θ))
  have hp : Function.Periodic g (2*Real.pi) := by
    intro θ
    simp only [g, angleJacobian, anglePoint, periodic_circleMap 0 r θ]
  have hi : (fun θ : ℝ => angleJacobian r θ * star (f (star (anglePoint r θ)))) =
      fun θ => g (-θ) := by
    funext θ
    dsimp only [g]
    rw [star_mul, angleJacobian_conj, neg_neg, anglePoint_conj]
    ring
  rw [hi, intervalIntegral.integral_comp_neg]
  have hs := hp.intervalIntegral_add_eq (-(2*Real.pi)) 0
  simp only [neg_add_cancel, zero_add] at hs
  rw [neg_zero, hs]
  exact intervalIntegral_conjugate _ _ _

end
end IsingBulk.First
