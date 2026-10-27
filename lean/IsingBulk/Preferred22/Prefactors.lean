import IsingBulk.Preferred22.Physical
import IsingBulk.Preferred22.Arithmetic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! Proper local magnetization branch lemmas, adapted from the pinned
MagnetizationBoundary module to the actual Preferred22 bulk definition. -/
namespace IsingBulk.Preferred22
noncomputable section
open Filter Set
open scoped Topology

theorem unit_inverse_power_argument_re_pos {z : ℂ} (hz : ‖z‖ = 1)
    (hfour : z^(4:ℕ) ≠ 1) : 0 < (1-(z^(4:ℕ))⁻¹).re := by
  have hn : ‖(z^(4:ℕ))⁻¹‖ = 1 := by rw [norm_inv,norm_pow,hz]; norm_num
  have hle : ((z^(4:ℕ))⁻¹).re ≤ 1 := by simpa only [hn] using Complex.re_le_norm ((z^(4:ℕ))⁻¹)
  have hne : ((z^(4:ℕ))⁻¹).re ≠ 1 := by
    intro heq
    have hi : ((z^(4:ℕ))⁻¹).im = 0 := Complex.abs_re_eq_norm.mp (by rw [heq,hn]; norm_num)
    have hone : (z^(4:ℕ))⁻¹ = 1 := Complex.ext (by simpa using heq) (by simpa using hi)
    exact hfour (inv_eq_one.mp hone)
  simpa only [Complex.sub_re,Complex.one_re] using sub_pos.mpr (lt_of_le_of_ne hle hne)

theorem magnetizationSquared_ne_zero_at_unit_nonaxis {z : ℂ} (hz : ‖z‖ = 1)
    (hfour : z^(4:ℕ) ≠ 1) : magnetizationSquared z ≠ 0 := by
  apply Complex.cpow_ne_zero_iff.mpr
  left
  intro heq
  have h := unit_inverse_power_argument_re_pos hz hfour
  rw [heq] at h
  norm_num at h

theorem magnetizationSquared_analyticAt_unit_nonaxis {z : ℂ} (hz : ‖z‖ = 1)
    (hfour : z^(4:ℕ) ≠ 1) : AnalyticAt ℂ magnetizationSquared z := by
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (by rw [hz]; norm_num)
  have ha : AnalyticAt ℂ (fun s : ℂ => 1-(s^(4:ℕ))⁻¹) z :=
    analyticAt_const.sub ((analyticAt_id.pow 4).inv (pow_ne_zero 4 hz0))
  have hp : (1-(z^(4:ℕ))⁻¹) ∈ Complex.slitPlane :=
    Or.inl (unit_inverse_power_argument_re_pos hz hfour)
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  have he := ha.eventually_analyticAt
  have hs := ha.continuousAt.eventually (Complex.isOpen_slitPlane.mem_nhds hp)
  filter_upwards [he,hs] with s has hsp
  exact has.differentiableAt.cpow_const hsp

theorem first_quadrant_pow_four_ne_one {z : ℂ} (hr : 0 < z.re) (hi : 0 < z.im) :
    z^(4:ℕ) ≠ 1 := by
  intro h
  have hp : (z-1)*(z+1)*(z-Complex.I)*(z+Complex.I) = 0 := by
    calc
      _ = (z^2-1)*(z^2-Complex.I^2) := by ring
      _ = z^4-1 := by rw [Complex.I_sq]; ring
      _ = 0 := sub_eq_zero.mpr h
  rcases mul_eq_zero.mp hp with h | h
  · rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · have := congrArg Complex.im (sub_eq_zero.mp h)
        simp only [Complex.one_im] at this
        linarith
      · have := congrArg Complex.im (eq_neg_of_add_eq_zero_left h)
        norm_num at this
        linarith
    · have := congrArg Complex.re (sub_eq_zero.mp h)
      simp only [Complex.I_re] at this
      linarith
  · have := congrArg Complex.re (eq_neg_of_add_eq_zero_left h)
    norm_num at this
    linarith


end
end IsingBulk.Preferred22
