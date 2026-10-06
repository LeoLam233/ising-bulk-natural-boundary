import IsingBulk.First.MeanPole
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! Clockwise rectangular residue normalization by explicit primitives.
The sign comes from the four displayed oriented sides, not a convention field. -/
namespace IsingBulk.First
noncomputable section
open Complex MeasureTheory Set intervalIntegral

/-- Top left-to-right, right downward, bottom right-to-left, left upward. -/
def clockwiseRectangle (delta top bottom : ℝ) (f : ℂ → ℂ) : ℂ :=
  (∫ x : ℝ in -delta..delta, f ((x:ℂ)+(top:ℂ)*I)) -
  (∫ x : ℝ in -delta..delta, f ((x:ℂ)+(bottom:ℂ)*I)) +
  I * (∫ y : ℝ in top..bottom, f ((delta:ℂ)+(y:ℂ)*I)) -
  I * (∫ y : ℝ in top..bottom, f (-(delta:ℂ)+(y:ℂ)*I))

private theorem horizontal_ne_zero (a x : ℝ) (ha : a ≠ 0) :
    (x:ℂ)+(a:ℂ)*I ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one,
    zero_mul, add_zero, zero_add] at hi
  exact ha hi

private theorem vertical_ne_zero (delta y : ℝ) (hd : delta ≠ 0) :
    (delta:ℂ)+(y:ℂ)*I ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  simp at hr
  exact hd hr

/-- A horizontal line avoids the logarithm cut whenever its height is nonzero. -/
theorem integral_horizontal_inv (delta a : ℝ) (ha : a ≠ 0) :
    (∫ x : ℝ in -delta..delta, ((x:ℂ)+(a:ℂ)*I)⁻¹) =
      log ((delta:ℂ)+(a:ℂ)*I) - log (-(delta:ℂ)+(a:ℂ)*I) := by
  have hc : Continuous (fun x : ℝ => ((x:ℂ)+(a:ℂ)*I)⁻¹) :=
    (Complex.continuous_ofReal.add continuous_const).inv₀ (fun x => horizontal_ne_zero a x ha)
  have hh : ∀ x : ℝ, HasDerivAt (fun x : ℝ => log ((x:ℂ)+(a:ℂ)*I))
      (((x:ℂ)+(a:ℂ)*I)⁻¹) x := by
    intro x
    have hs : (x:ℂ)+(a:ℂ)*I ∈ slitPlane := Or.inr (by simpa using ha)
    simpa using (((hasDerivAt_id (x:ℂ)).add_const ((a:ℂ)*I)).clog hs).comp_ofReal
  simpa only [Complex.ofReal_neg] using integral_eq_sub_of_hasDerivAt
    (fun x _ => hh x) (hc.intervalIntegrable (-delta) delta)

/-- The right side uses the ordinary logarithm in its right half-plane. -/
theorem integral_right_inv (delta a b : ℝ) (hd : 0 < delta) :
    I * (∫ y : ℝ in a..b, ((delta:ℂ)+(y:ℂ)*I)⁻¹) =
      log ((delta:ℂ)+(b:ℂ)*I) - log ((delta:ℂ)+(a:ℂ)*I) := by
  rw [← intervalIntegral.integral_const_mul]
  have hc : Continuous (fun y : ℝ => I * ((delta:ℂ)+(y:ℂ)*I)⁻¹) :=
    continuous_const.mul ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).inv₀
      (fun y => vertical_ne_zero delta y (ne_of_gt hd)))
  apply integral_eq_sub_of_hasDerivAt _ (hc.intervalIntegrable a b)
  intro y _
  have hs : (delta:ℂ)+(y:ℂ)*I ∈ slitPlane := Or.inl (by simpa using hd)
  simpa [div_eq_mul_inv] using
    ((((hasDerivAt_id (y:ℂ)).mul_const I).const_add (delta:ℂ)).clog hs).comp_ofReal

/-- On the left side use log(-z); its derivative is still 1/z. -/
theorem integral_left_inv (delta a b : ℝ) (hd : 0 < delta) :
    I * (∫ y : ℝ in a..b, (-(delta:ℂ)+(y:ℂ)*I)⁻¹) =
      log ((delta:ℂ)-(b:ℂ)*I) - log ((delta:ℂ)-(a:ℂ)*I) := by
  rw [← intervalIntegral.integral_const_mul]
  have hc : Continuous (fun y : ℝ => I * (-(delta:ℂ)+(y:ℂ)*I)⁻¹) :=
    continuous_const.mul ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).inv₀
      (fun y => by simpa using vertical_ne_zero (-delta) y (neg_ne_zero.mpr (ne_of_gt hd))))
  apply integral_eq_sub_of_hasDerivAt _ (hc.intervalIntegrable a b)
  intro y _
  have hs : (delta:ℂ)-(y:ℂ)*I ∈ slitPlane := Or.inl (by simpa using hd)
  have hh := ((((hasDerivAt_id (y:ℂ)).mul_const I).const_sub (delta:ℂ)).clog hs).comp_ofReal
  have hder : -I / ((delta:ℂ)-(y:ℂ)*I) = I * (-(delta:ℂ)+(y:ℂ)*I)⁻¹ := by
    rw [show (delta:ℂ)-(y:ℂ)*I = -(-(delta:ℂ)+(y:ℂ)*I) by ring]
    simp only [div_eq_mul_inv, inv_neg, neg_mul_neg]
  simpa only [id_eq, one_mul, hder] using hh

theorem log_neg_of_im_pos (z : ℂ) (hz : 0 < z.im) :
    log (-z) = log z - (Real.pi:ℂ)*I := by
  apply Complex.ext
  · simp [Complex.log_re]
  · simp [Complex.log_im, arg_neg_eq_arg_sub_pi_of_im_pos hz]

theorem log_neg_of_im_neg (z : ℂ) (hz : z.im < 0) :
    log (-z) = log z + (Real.pi:ℂ)*I := by
  apply Complex.ext
  · simp [Complex.log_re]
  · simp [Complex.log_im, arg_neg_eq_arg_add_pi_of_im_neg hz]

/-- Genuine oriented contour computation of the inverse kernel. -/
theorem clockwiseRectangle_inv (delta top bottom : ℝ)
    (hd : 0 < delta) (ht : 0 < top) (hb : bottom < 0) :
    clockwiseRectangle delta top bottom (fun z => z⁻¹) = -2*(Real.pi:ℂ)*I := by
  unfold clockwiseRectangle
  rw [integral_horizontal_inv delta top (ne_of_gt ht),
    integral_horizontal_inv delta bottom (ne_of_lt hb), integral_right_inv delta top bottom hd,
    integral_left_inv delta top bottom hd]
  have htop := log_neg_of_im_pos (-(delta:ℂ)+(top:ℂ)*I) (by simpa using ht)
  have hbot := log_neg_of_im_neg (-(delta:ℂ)+(bottom:ℂ)*I) (by simpa using hb)
  rw [show (delta:ℂ)-(top:ℂ)*I = -(-(delta:ℂ)+(top:ℂ)*I) by ring,
    show (delta:ℂ)-(bottom:ℂ)*I = -(-(delta:ℂ)+(bottom:ℂ)*I) by ring, htop, hbot]
  ring

end
end IsingBulk.First
