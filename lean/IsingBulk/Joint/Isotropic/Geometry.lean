import IsingBulk.Joint.Slices.ExactDomains
import IsingBulk.Anisotropic.Geometry.IsotropicDomains
import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace IsingBulk.Joint
noncomputable section
open IsingBulk.Anisotropic

theorem isotropic_spectral_iff (z : ℂ) :
    ratioSlice 1 z ∈ Joint.spectralSet ↔ ‖Complex.sinh z‖ = 1 :=
  mem_spectralSet_one_iff z

theorem isotropic_high_iff (z : ℂ) :
    ratioSlice 1 z ∈ highDomain ↔ |z.im| < Real.pi / 2 ∧ ‖Complex.sinh z‖ < 1 := by
  change z ∈ ratioSlice 1 ⁻¹' highDomain ↔ _
  rw [highDomain_pullback (by norm_num : (0:ℝ)<1), mem_omegaH_one_iff]

theorem isotropic_low_iff (z : ℂ) :
    ratioSlice 1 z ∈ lowDomain ↔ 0 < z.re ∧ 1 < ‖Complex.sinh z‖ := by
  change z ∈ ratioSlice 1 ⁻¹' lowDomain ↔ _
  rw [lowDomain_pullback (by norm_num : (0:ℝ)<1), mem_omegaL_one_iff]

theorem cosh_re_formula (z : ℂ) :
    (Complex.cosh z).re = Real.cosh z.re * Real.cos z.im := by
  conv_lhs => rw [← Complex.re_add_im z, Complex.cosh_add, Complex.cosh_mul_I,
    Complex.sinh_mul_I]
  simp [Complex.cosh_ofReal_re, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

theorem cosh_re_pos_central {z : ℂ} (hz : |z.im| < Real.pi / 2) :
    0 < (Complex.cosh z).re := by
  rw [cosh_re_formula]
  exact mul_pos (Real.cosh_pos _) (Real.cos_pos_of_mem_Ioo (abs_lt.mp hz))

theorem sinh_injOn_central :
    Set.InjOn Complex.sinh {z : ℂ | |z.im| < Real.pi / 2} := by
  intro z hz w hw he
  change |z.im| < Real.pi / 2 at hz
  change |w.im| < Real.pi / 2 at hw
  have hs : Complex.cosh z ^ 2 = Complex.cosh w ^ 2 := by
    rw [Complex.cosh_sq, Complex.cosh_sq, he]
  have hc : Complex.cosh z = Complex.cosh w := by
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hs with h | h
    · exact h
    · have hr := congrArg Complex.re h
      simp only [Complex.neg_re] at hr
      linarith [cosh_re_pos_central hz, cosh_re_pos_central hw]
  have hex : Complex.exp z = Complex.exp w := by
    rw [← Complex.cosh_add_sinh, ← Complex.cosh_add_sinh, hc, he]
  apply Complex.exp_inj_of_neg_pi_lt_of_le_pi _ _ _ _ hex
  all_goals have hp := Real.pi_pos
  · linarith [(abs_lt.mp hz).1]
  · linarith [(abs_lt.mp hz).2]
  · linarith [(abs_lt.mp hw).1]
  · linarith [(abs_lt.mp hw).2]

theorem sinh_injOn_highSlice : Set.InjOn Complex.sinh (omegaH 1) :=
  sinh_injOn_central.mono (fun _ hz => ((mem_omegaH_one_iff _).mp hz).1)

end
end IsingBulk.Joint
