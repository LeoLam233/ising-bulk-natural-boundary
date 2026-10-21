import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! The sharp scalar bound behind the HT critical lower derivative.
This concerns the actual odd radial power 2k-1. It does not replace the
required source localization, mean-error, and complement attachment. -/
namespace IsingBulk.HT.First
noncomputable section
open MeasureTheory Set
open scoped Interval

/-- All critical lower-pole orders are dominated by one logarithmic kernel. -/
theorem odd_radial_critical_kernel_le {k : ℕ} (hk : 1 ≤ k)
    {epsilon r : ℝ} (he : 0 < epsilon) (hr : 0 ≤ r) :
    r^(2*k-1)/(epsilon+r^2)^k ≤ r/(epsilon+r^2) := by
  have hd : 0 < epsilon+r^2 := add_pos_of_pos_of_nonneg he (sq_nonneg r)
  have hratio : r^2/(epsilon+r^2) ≤ 1 := (div_le_one hd).mpr (by linarith)
  have hnonneg : 0 ≤ r^2/(epsilon+r^2) := div_nonneg (sq_nonneg r) hd.le
  have hpow : (r^2/(epsilon+r^2))^(k-1) ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ hnonneg hratio (k-1)
  have heq : r^(2*k-1)/(epsilon+r^2)^k =
      (r/(epsilon+r^2))*(r^2/(epsilon+r^2))^(k-1) := by
    have hnum : r^(2*k-1)=r*(r^2)^(k-1) := by
      rw [show 2*k-1=1+2*(k-1) by omega, pow_add, pow_one, pow_mul]
    have hdenpow : (epsilon+r^2)^k=(epsilon+r^2)*(epsilon+r^2)^(k-1) := by
      calc
        _ = (epsilon+r^2)^(1+(k-1)) := congrArg ((epsilon+r^2)^·) (by omega)
        _ = _ := by rw [pow_add, pow_one]
    rw [hnum, hdenpow, div_pow]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heq]
  exact (mul_le_mul_of_nonneg_left hpow (div_nonneg hr hd.le)).trans_eq (mul_one _)

/-- Exact logarithmic primitive for the remaining positive radial kernel. -/
theorem integral_radial_log_kernel {epsilon R : ℝ} (he : 0 < epsilon) (_hR : 0 ≤ R) :
    (∫ r in (0:ℝ)..R, r/(epsilon+r^2)) =
      (Real.log (epsilon+R^2)-Real.log epsilon)/2 := by
  have hder (r : ℝ) (_hr : r ∈ uIcc (0:ℝ) R) :
      HasDerivAt (fun x : ℝ => Real.log (epsilon+x^2)/2) (r/(epsilon+r^2)) r := by
    have hd : epsilon+r^2 ≠ 0 := (add_pos_of_pos_of_nonneg he (sq_nonneg r)).ne'
    have hh := ((Real.hasDerivAt_log hd).comp r
      (((hasDerivAt_id r).pow 2).const_add epsilon)).div_const 2
    convert! hh using 1
    all_goals simp
    all_goals ring
  have hc : Continuous (fun r : ℝ => r/(epsilon+r^2)) := by
    apply continuous_id.div (continuous_const.add (continuous_id.pow 2))
    intro r
    exact (add_pos_of_pos_of_nonneg he (sq_nonneg r)).ne'
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hder (hc.intervalIntegrable _ _)
  simpa only [zero_pow (by decide : 2 ≠ 0), add_zero, sub_div] using hh

/-- No epsilon loss: the odd critical lower derivative costs only a logarithm. -/
theorem integral_odd_radial_critical_le {k : ℕ} (hk : 1 ≤ k)
    {epsilon R : ℝ} (he : 0 < epsilon) (hR : 0 ≤ R) :
    (∫ r in (0:ℝ)..R, r^(2*k-1)/(epsilon+r^2)^k) ≤
      (Real.log (epsilon+R^2)-Real.log epsilon)/2 := by
  have hden (r : ℝ) : epsilon+r^2 ≠ 0 :=
    (add_pos_of_pos_of_nonneg he (sq_nonneg r)).ne'
  have hf : Continuous (fun r : ℝ => r^(2*k-1)/(epsilon+r^2)^k) :=
    (continuous_id.pow _).div ((continuous_const.add (continuous_id.pow 2)).pow k)
      (fun r => pow_ne_zero _ (hden r))
  have hg : Continuous (fun r : ℝ => r/(epsilon+r^2)) :=
    continuous_id.div (continuous_const.add (continuous_id.pow 2)) hden
  have hh := intervalIntegral.integral_mono_on (μ := volume) hR (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)
    (fun r hr => odd_radial_critical_kernel_le hk he hr.1)
  rw [integral_radial_log_kernel he hR] at hh
  exact hh

end
end IsingBulk.HT.First
