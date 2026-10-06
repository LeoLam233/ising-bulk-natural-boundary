import IsingBulk.First.MeanPhase
import Mathlib.Analysis.Complex.Exponential

/-! Quantitative conversion from the actual attenuation/phase inequalities
into the required nonlinear denominator estimate. This is an auxiliary theorem;
constructing those inequalities for the physical phase remains separate. -/
namespace IsingBulk.First
noncomputable section

/-- A no-wrapping lower bound obtained directly from the exponential's
quadratic remainder. -/
theorem norm_one_sub_exp_lower {w : ℂ} (hw : ‖w‖ ≤ 1/2) :
    ‖w‖ / 2 ≤ ‖1-Complex.exp w‖ := by
  have he := Complex.norm_exp_sub_one_sub_id_le (show ‖w‖ ≤ 1 by linarith)
  have ht : ‖w‖ ≤ ‖Complex.exp w-1‖ + ‖Complex.exp w-1-w‖ := by
    calc
      ‖w‖ = ‖(Complex.exp w-1)-(Complex.exp w-1-w)‖ := by congr 1; ring
      _ ≤ _ := norm_sub_le _ _
  rw [norm_sub_rev (Complex.exp w) 1] at ht
  have hn := norm_nonneg w
  nlinarith

/-- Combining attenuation O(epsilon) and the zero-sum concave-phase
separation O(q), with an O(epsilon²) central error. No linearized denominator
is substituted for the actual exponential. -/
theorem nonlinear_exp_gap {w : ℂ} {epsilon q a b C : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hC : 0 ≤ C)
    (he : 0 ≤ epsilon) (he1 : epsilon ≤ 1)
    (hw : ‖w‖ ≤ 1/2)
    (hattenuation : w.re ≤ -a*epsilon)
    (hphase : b*q-C*epsilon^2 ≤ w.im) :
    (a*b/(2*(a+b+C))) * (epsilon+q) ≤ ‖1-Complex.exp w‖ := by
  have hre := (Complex.abs_re_le_norm w)
  have him := (Complex.abs_im_le_norm w)
  have hr : a*epsilon ≤ ‖w‖ := by
    have := (abs_le.mp hre).1
    linarith
  have hi : b*q ≤ ‖w‖ + C*epsilon := by
    have hi' := (abs_le.mp him).2
    have he2 : epsilon^2 ≤ epsilon := by nlinarith
    have hc2 := mul_le_mul_of_nonneg_left he2 hC
    linarith
  have hh := norm_one_sub_exp_lower hw
  have hden : 0 < 2*(a+b+C) := by positivity
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).mpr
  have h1 := mul_le_mul_of_nonneg_left hr hb.le
  have h2 := mul_le_mul_of_nonneg_left hi ha.le
  have h3 := mul_le_mul_of_nonneg_left hr hC
  have h4 := mul_le_mul_of_nonneg_left hh (show 0 ≤ 2*(a+b+C) by positivity)
  nlinarith

/-- The explicit constant in the nonlinear gap is strictly positive. -/
theorem nonlinear_exp_gap_constant_pos {a b C : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hC : 0 ≤ C) : 0 < a*b/(2*(a+b+C)) := by
  exact div_pos (mul_pos ha hb) (by positivity)

end
end IsingBulk.First
