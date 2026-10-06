import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Tactic

/-! A genuine local inverse-temperature continuation on the right half-plane.
No assertion of single-valuedness on the whole exterior is made. -/
namespace IsingBulk.Final
noncomputable section
open Complex Set Filter
open scoped Topology

def arsinhRight (s : ℂ) : ℂ := Complex.log (s+Complex.sqrt (1+s^2))
def inverseTemperatureBranch (J : ℝ) (s : ℂ) : ℂ := arsinhRight s / (2*(J:ℂ))

theorem sqrt_re_nonneg (w : ℂ) : 0 ≤ (Complex.sqrt w).re := by
  rw [Complex.sqrt,Complex.cpow_inv_two_re]
  exact Real.sqrt_nonneg _

theorem arsinh_square_argument_slit {s : ℂ} (hs : 0 < s.re) :
    1+s^2 ∈ Complex.slitPlane := by
  by_cases hi : s.im=0
  · left
    simp only [pow_two,Complex.add_re,Complex.one_re,Complex.mul_re,hi,mul_zero,sub_zero]
    positivity
  · right
    have he : (1+s^2).im = 2*s.re*s.im := by simp [pow_two]; ring
    rw [he]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hs.ne') hi

theorem arsinh_log_argument_slit {s : ℂ} (hs : 0 < s.re) :
    s+Complex.sqrt (1+s^2) ∈ Complex.slitPlane := by
  left
  simpa only [Complex.add_re] using add_pos_of_pos_of_nonneg hs (sqrt_re_nonneg _)

theorem arsinhRight_analyticAt {s : ℂ} (hs : 0 < s.re) : AnalyticAt ℂ arsinhRight s := by
  have hsqrt : AnalyticAt ℂ Complex.sqrt (1+s^2) :=
    Complex.differentiableOn_sqrt.analyticAt
      (Complex.isOpen_slitPlane.mem_nhds (arsinh_square_argument_slit hs))
  have hp : AnalyticAt ℂ (fun t : ℂ => 1+t^2) s :=
    analyticAt_const.add (analyticAt_id.pow 2)
  have hf : AnalyticAt ℂ (fun t : ℂ => t+Complex.sqrt (1+t^2)) s :=
    analyticAt_id.add (hsqrt.comp (f := fun t : ℂ => 1+t^2) hp)
  exact (analyticAt_clog (arsinh_log_argument_slit hs)).comp
    (f := fun t : ℂ => t+Complex.sqrt (1+t^2)) hf

theorem arsinhRight_ne_zero {s : ℂ} (hs : 0 < s.re) : arsinhRight s ≠ 0 := by
  intro hzero
  change Complex.log (s+Complex.sqrt (1+s^2))=0 at hzero
  have harg : s+Complex.sqrt (1+s^2) ≠ 0 := Complex.slitPlane_ne_zero (arsinh_log_argument_slit hs)
  have he : s+Complex.sqrt (1+s^2)=1 := by
    simpa only [hzero,Complex.exp_zero] using (Complex.exp_log harg).symm
  have hr : Complex.sqrt (1+s^2)=1-s := by linear_combination he
  have hsq : (Complex.sqrt (1+s^2))^2=1+s^2 :=
    Complex.cpow_nat_inv_pow _ (by decide : (2:ℕ) ≠ 0)
  rw [hr] at hsq
  have hz : (2:ℂ)*s=0 := by linear_combination -hsq
  have hs0 : s=0 := (mul_eq_zero.mp hz).resolve_left (by norm_num)
  rw [hs0] at hs
  norm_num at hs

theorem inverseTemperatureBranch_regular {s : ℂ} (hs : 0 < s.re) {J : ℝ} (hJ : 0 < J) :
    AnalyticAt ℂ (inverseTemperatureBranch J) s ∧ inverseTemperatureBranch J s ≠ 0 := by
  have hj0 : (2*(J:ℂ)) ≠ 0 := mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr hJ.ne')
  exact ⟨(arsinhRight_analyticAt hs).div analyticAt_const hj0,
    div_ne_zero (arsinhRight_ne_zero hs) hj0⟩

/-- This is the real low-temperature inverse-temperature branch. -/
theorem arsinhRight_real {x : ℝ} (hx : 0 ≤ x) :
    arsinhRight (x:ℂ) = (Real.arsinh x:ℂ) := by
  have hsq : Complex.sqrt (1+(x:ℂ)^2) = (Real.sqrt (1+x^2):ℂ) := by
    have h := Complex.sqrt_of_nonneg
      (a := ((1+x^2:ℝ):ℂ)) (Complex.zero_le_real.mpr (by positivity))
    simp only [Complex.ofReal_re] at h
    simpa only [Complex.ofReal_add,Complex.ofReal_one,Complex.ofReal_pow] using h
  unfold arsinhRight Real.arsinh
  rw [hsq,← Complex.ofReal_add,← Complex.ofReal_log (add_nonneg hx (Real.sqrt_nonneg _))]

/-- The constructed branch really inverts the source temperature coordinate. -/
theorem sinh_arsinhRight {s : ℂ} (hs : 0 < s.re) : Complex.sinh (arsinhRight s)=s := by
  have harg : s+Complex.sqrt (1+s^2) ≠ 0 := Complex.slitPlane_ne_zero (arsinh_log_argument_slit hs)
  have hsq : (Complex.sqrt (1+s^2))^2=1+s^2 :=
    Complex.cpow_nat_inv_pow _ (by decide : (2:ℕ) ≠ 0)
  have hmul : (Complex.sqrt (1+s^2)-s)*(s+Complex.sqrt (1+s^2))=1 := by
    linear_combination hsq
  have hinv : (s+Complex.sqrt (1+s^2))⁻¹=Complex.sqrt (1+s^2)-s :=
    inv_eq_of_mul_eq_one_left hmul
  unfold arsinhRight Complex.sinh
  rw [Complex.exp_neg,Complex.exp_log harg,hinv]
  ring

theorem inverseTemperatureBranch_real {x J : ℝ} (hx : 0 ≤ x) :
    inverseTemperatureBranch J (x:ℂ) = (Real.arsinh x/(2*J):ℂ) := by
  simp only [inverseTemperatureBranch,arsinhRight_real hx]

theorem inverseTemperatureBranch_relation {s : ℂ} (hs : 0 < s.re) {J : ℝ} (hJ : 0 < J) :
    Complex.sinh (2*(J:ℂ)*inverseTemperatureBranch J s)=s := by
  have hj0 : 2*(J:ℂ) ≠ 0 := mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr hJ.ne')
  rw [inverseTemperatureBranch,mul_div_cancel₀ _ hj0,sinh_arsinhRight hs]

end
end IsingBulk.Final
