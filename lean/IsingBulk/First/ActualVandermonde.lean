import IsingBulk.First.ShapeVandermonde
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-! Exact coincidence-safe angular Vandermonde factorization. The regular
factor is defined with real sinc and remains continuous when coordinates meet. -/
namespace IsingBulk.First
noncomputable section
open Complex
open scoped BigOperators

theorem real_mul_sinc (x : ℝ) : x * Real.sinc x = Real.sin x := by
  by_cases h : x = 0
  · simp [h]
  · rw [Real.sinc_of_ne_zero h]
    field_simp

def angularDifferenceFactor (u v : ℝ) : ℂ :=
  I * exp (((u+v)/2 : ℝ) * I) * (Real.sinc ((u-v)/2) : ℂ)

theorem exp_angle_sub_exact (u v : ℝ) :
    exp ((u:ℂ)*I) - exp ((v:ℂ)*I) =
      ((u-v:ℝ):ℂ) * angularDifferenceFactor u v := by
  have h₁ : (u:ℂ)*I = (((u+v)/2:ℝ):ℂ)*I + (((u-v)/2:ℝ):ℂ)*I := by push_cast; ring
  have h₂ : (v:ℂ)*I = (((u+v)/2:ℝ):ℂ)*I + -((((u-v)/2:ℝ):ℂ)*I) := by push_cast; ring
  have hd (x : ℝ) : exp ((x:ℂ)*I) - exp (-(x:ℂ)*I) =
      2 * (Real.sin x:ℂ) * I := by
    simp only [exp_mul_I, cos_neg, sin_neg, ← ofReal_sin]
    ring
  have hs : ((u-v:ℝ):ℂ) * (Real.sinc ((u-v)/2):ℂ) =
      2 * (Real.sin ((u-v)/2):ℂ) := by
    exact_mod_cast (show (u-v)*Real.sinc ((u-v)/2) = 2*Real.sin ((u-v)/2) by
      have h := real_mul_sinc ((u-v)/2)
      nlinarith)
  calc
    _ = exp ((((u+v)/2:ℝ):ℂ)*I) *
        (exp ((((u-v)/2:ℝ):ℂ)*I) - exp (-(((u-v)/2:ℝ):ℂ)*I)) := by
      rw [h₁, h₂, exp_add, exp_add, neg_mul]
      ring
    _ = exp ((((u+v)/2:ℝ):ℂ)*I) * (2*(Real.sin ((u-v)/2):ℂ)*I) := by rw [hd]
    _ = _ := by
      unfold angularDifferenceFactor
      linear_combination -I * exp ((((u+v)/2:ℝ):ℂ)*I) * hs

theorem angularDifferenceFactor_continuous :
    Continuous (fun p : ℝ × ℝ => angularDifferenceFactor p.1 p.2) := by
  unfold angularDifferenceFactor
  apply Continuous.mul
  · fun_prop
  · exact Complex.continuous_ofReal.comp (Real.continuous_sinc.comp (by fun_prop))

/-- The phase from the two angular differences cancels exactly against yᵢyⱼ. -/
theorem angular_pair_squared (u v : ℝ) :
    -(exp ((u:ℂ)*I)-exp ((v:ℂ)*I))^2 /
        (exp ((u:ℂ)*I)*exp ((v:ℂ)*I)) =
      ((u-v:ℝ):ℂ)^2 * (Real.sinc ((u-v)/2):ℂ)^2 := by
  rw [exp_angle_sub_exact]
  have he : exp ((((u+v)/2:ℝ):ℂ)*I)^2 = exp ((u:ℂ)*I)*exp ((v:ℂ)*I) := by
    rw [pow_two, ← exp_add, ← exp_add]
    congr 1
    push_cast
    ring
  unfold angularDifferenceFactor
  simp only [mul_pow, I_sq, he]
  field_simp

end
end IsingBulk.First
