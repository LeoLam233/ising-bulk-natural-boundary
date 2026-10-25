import IsingBulk.Joint.Isotropic.Geometry
import IsingBulk.HT.Final.PhysicalTemperature

namespace IsingBulk.Joint
noncomputable section
open IsingBulk.Anisotropic IsingBulk.Final IsingBulk.HT.Final

theorem sinh_arsinhRight_strip {s : ℂ} (hs : |s.im| < 1) :
    Complex.sinh (arsinhRight s) = s := by
  have hn : s + Complex.sqrt (1+s^2) ≠ 0 :=
    Complex.slitPlane_ne_zero (Or.inl (temperature_log_argument_re_pos hs))
  have hsq : (Complex.sqrt (1+s^2))^2 = 1+s^2 :=
    Complex.cpow_nat_inv_pow _ (by decide : (2:ℕ) ≠ 0)
  have hi : (s+Complex.sqrt (1+s^2))⁻¹ = Complex.sqrt (1+s^2)-s := by
    apply inv_eq_of_mul_eq_one_right
    linear_combination hsq
  unfold arsinhRight Complex.sinh
  rw [Complex.exp_neg, Complex.exp_log hn, hi]
  ring

theorem arsinhRight_mem_high {s : ℂ} (hs : ‖s‖ < 1) :
    arsinhRight s ∈ omegaH 1 := by
  have him := (Complex.abs_im_le_norm s).trans_lt hs
  rw [mem_omegaH_one_iff, sinh_arsinhRight_strip him]
  refine ⟨?_,hs⟩
  rw [arsinhRight, Complex.log_im]
  exact Complex.abs_arg_lt_pi_div_two_iff.mpr
    (Or.inl (temperature_log_argument_re_pos him))

theorem sinh_bijOn_high :
    Set.BijOn Complex.sinh (omegaH 1) {s : ℂ | ‖s‖ < 1} := by
  refine ⟨fun z hz => ((mem_omegaH_one_iff z).mp hz).2, sinh_injOn_highSlice, ?_⟩
  intro s hs
  exact ⟨arsinhRight s, arsinhRight_mem_high hs,
    sinh_arsinhRight_strip ((Complex.abs_im_le_norm s).trans_lt hs)⟩

theorem arsinhRight_sinh_high {z : ℂ} (hz : z ∈ omegaH 1) :
    arsinhRight (Complex.sinh z) = z := by
  have hn := ((mem_omegaH_one_iff z).mp hz).2
  apply sinh_injOn_highSlice (arsinhRight_mem_high hn) hz
  exact sinh_arsinhRight_strip ((Complex.abs_im_le_norm _).trans_lt hn)

/-- Both holomorphic directions of the exact high-temperature biholomorphism. -/
theorem high_biholomorphism :
    Set.BijOn Complex.sinh (omegaH 1) {s : ℂ | ‖s‖ < 1} ∧
    AnalyticOnNhd ℂ Complex.sinh (omegaH 1) ∧
    AnalyticOnNhd ℂ arsinhRight {s : ℂ | ‖s‖ < 1} ∧
    (∀ z ∈ omegaH 1, arsinhRight (Complex.sinh z) = z) := by
  refine ⟨sinh_bijOn_high, fun _ _ => Complex.analyticAt_sinh, ?_,
    fun _ hz => arsinhRight_sinh_high hz⟩
  intro s hs
  exact arsinhRight_analyticAt_strip ((Complex.abs_im_le_norm s).trans_lt hs)

end
end IsingBulk.Joint
