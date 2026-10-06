import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-! Explicit logarithmic L1 integrals for the square of the physical branch
one-body majorant. All constants are independent of the radial epsilon. -/
namespace IsingBulk.Tail
noncomputable section
open MeasureTheory Set
open scoped Topology

theorem reciprocal_abs_continuous {e : ℝ} (he : 0 < e) :
    Continuous (fun u : ℝ => (|u|+e)⁻¹) := by
  apply (continuous_abs.add continuous_const).inv₀
  intro u
  exact (add_pos_of_nonneg_of_pos (abs_nonneg u) he).ne'

theorem reciprocal_positive_integral {a e : ℝ} (ha : 0 ≤ a) (he : 0 < e) :
    (∫ u : ℝ in 0..a, (|u|+e)⁻¹) = Real.log ((a+e)/e) := by
  have hEq : (∫ u : ℝ in 0..a, (|u|+e)⁻¹) = ∫ u : ℝ in 0..a, (u+e)⁻¹ := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ha] at hu
    dsimp only
    rw [abs_of_nonneg hu.1]
  rw [hEq,intervalIntegral.integral_comp_add_right]
  simpa only [zero_add] using integral_inv_of_pos he (add_pos_of_nonneg_of_pos ha he)

theorem reciprocal_abs_symmetric_integral {a e : ℝ} (ha : 0 ≤ a) (he : 0 < e) :
    (∫ u : ℝ in -a..a, (|u|+e)⁻¹) = 2*Real.log ((a+e)/e) := by
  have hc := reciprocal_abs_continuous he
  have hn : (∫ u : ℝ in -a..0, (|u|+e)⁻¹) = ∫ u : ℝ in 0..a, (|u|+e)⁻¹ := by
    simpa only [neg_zero,abs_neg] using
      (intervalIntegral.integral_comp_neg (fun u : ℝ => (|u|+e)⁻¹) (a := 0) (b := a)).symm
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (a := -a) (b := 0)) (hc.intervalIntegrable (a := 0) (b := a)),
    hn,reciprocal_positive_integral ha he]
  ring

theorem reciprocal_shifted_integral_le {P e b : ℝ} (hP : 0 ≤ P) (he : 0 < e)
    (hb : |b| ≤ P) :
    (∫ u : ℝ in -P..P, (|u-b|+e)⁻¹) ≤ 2*Real.log ((2*P+e)/e) := by
  have hc := reciprocal_abs_continuous he
  have hb' := abs_le.mp hb
  rw [intervalIntegral.integral_comp_sub_right (fun u : ℝ => (|u|+e)⁻¹) b]
  calc
    _ ≤ ∫ u : ℝ in -(2*P)..(2*P), (|u|+e)⁻¹ := by
      apply intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
        (Filter.Eventually.of_forall (fun u => inv_nonneg.mpr (by positivity)))
        (hc.intervalIntegrable (-(2*P)) (2*P))
    _ = _ := reciprocal_abs_symmetric_integral (by positivity) he

/-- Uniform logarithmic form when epsilon is at most one. -/
theorem reciprocal_shifted_log_bound {P e b : ℝ} (hP : 0 ≤ P) (he : 0 < e)
    (he1 : e ≤ 1) (hb : |b| ≤ P) :
    (∫ u : ℝ in -P..P, (|u-b|+e)⁻¹) ≤
      2*(Real.log (2*P+1)+Real.log (1/e)) := by
  apply (reciprocal_shifted_integral_le hP he hb).trans
  have hlog : Real.log (2*P+e) ≤ Real.log (2*P+1) :=
    Real.log_le_log (by positivity) (by linarith)
  rw [Real.log_div (by positivity : 2*P+e ≠ 0) he.ne',one_div,Real.log_inv]
  linarith

end
end IsingBulk.Tail
