import IsingBulk.Analysis.BranchModulus
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-! Size of the actual logarithmic branch phase near W=1. This supplies
microcore radius control and does not replace phase geometry by a model. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch Filter
open scoped Topology

 theorem lowerArccos_norm_upper (W : ℂ) (hsmall : ‖1-W‖ ≤ 1/100) :
    ‖lowerArccos W‖ ≤ 6*Real.sqrt ‖1-W‖ := by
  let d := ‖1-W‖
  have hd : 0 ≤ d := norm_nonneg _
  have hs : (Real.sqrt d)^2=d := Real.sq_sqrt hd
  have hspos : 0 ≤ Real.sqrt d := Real.sqrt_nonneg d
  have hsbound : Real.sqrt d ≤ 1/10 := by nlinarith
  have hdroot : d ≤ Real.sqrt d := by nlinarith
  have hother : ‖1+W‖ ≤ 3 := by
    have hh := norm_add_le (1-W) (W+1)
    have hh' := norm_sub_le (2:ℂ) (1-W)
    have he : (2:ℂ)-(1-W)=1+W := by ring
    rw [he] at hh'
    norm_num at hh'
    nlinarith
  have hH : ‖1-W^2‖ ≤ 3*d := by
    rw [show 1-W^2=(1-W)*(1+W) by ring,norm_mul]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hother hd
  have hsq : ‖Complex.sqrt (1-W^2)‖^2=‖1-W^2‖ := by rw [← norm_pow,sqrt_sq]
  have hsqbound : ‖Complex.sqrt (1-W^2)‖ ≤ 2*Real.sqrt d := by
    nlinarith [norm_nonneg (Complex.sqrt (1-W^2))]
  have hroot : ‖inverseCosineRoot W-1‖ ≤ 3*Real.sqrt d := by
    have he : inverseCosineRoot W-1=(W-1)+Complex.I*Complex.sqrt (1-W^2) := by
      unfold inverseCosineRoot
      ring
    rw [he]
    have hh := norm_add_le (W-1) (Complex.I*Complex.sqrt (1-W^2))
    rw [norm_mul,Complex.norm_I,one_mul,norm_sub_rev W 1] at hh
    nlinarith
  have hlog := Complex.norm_log_one_add_half_le_self
    (z := inverseCosineRoot W-1) (by nlinarith : ‖inverseCosineRoot W-1‖ ≤ 1/2)
  have he : 1+(inverseCosineRoot W-1)=inverseCosineRoot W := by ring
  rw [he] at hlog
  rw [lowerArccos,norm_mul,norm_neg,Complex.norm_I,one_mul]
  nlinarith

 theorem cos_quadratic_norm_bound : ∃ C r : ℝ, 0 < C ∧ 0 < r ∧ ∀ φ : ℂ,
    ‖φ‖ < r → ‖1-Complex.cos φ‖ ≤ C*‖φ‖^2 := by
  obtain ⟨C,hC,hbound⟩ := analytic_quadratic_remainder Complex.cos (by fun_prop)
  obtain ⟨r,hr,hrbound⟩ := Metric.eventually_nhds_iff.mp hbound
  refine ⟨C,r,hC,hr,?_⟩
  intro φ hφ
  have hh := hrbound (y := φ) (by simpa using hφ)
  rw [fderiv_eq_deriv_mul,Complex.deriv_cos] at hh
  simpa [norm_sub_rev] using hh

 theorem lowerArccos_norm_lower : ∃ c r : ℝ, 0 < c ∧ 0 < r ∧ ∀ W : ℂ,
    ‖1-W‖ < r → c*Real.sqrt ‖1-W‖ ≤ ‖lowerArccos W‖ := by
  obtain ⟨C,ρ,hC,hρ,hcos⟩ := cos_quadratic_norm_bound
  let r := min (1/100:ℝ) ((ρ/12)^2)
  have hr : 0 < r := lt_min (by norm_num) (sq_pos_of_pos (by positivity))
  refine ⟨1/Real.sqrt C,r,by positivity,hr,?_⟩
  intro W hW
  have hu := lowerArccos_norm_upper W (hW.le.trans (min_le_left _ _))
  have hs : (Real.sqrt ‖1-W‖)^2=‖1-W‖ := Real.sq_sqrt (norm_nonneg _)
  have hρsqrt : Real.sqrt ‖1-W‖ < ρ/12 := by
    have he := hW.trans_le (min_le_right _ _)
    nlinarith [Real.sqrt_nonneg ‖1-W‖]
  have hφ : ‖lowerArccos W‖ < ρ := by nlinarith
  have hb := hcos (lowerArccos W) hφ
  rw [cos_lowerArccos] at hb
  have hCs := Real.sq_sqrt hC.le
  have hsqrt : Real.sqrt ‖1-W‖ ≤ Real.sqrt C*‖lowerArccos W‖ := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg _),?_⟩
    rw [mul_pow,hCs]
    exact hb
  have hp := Real.sqrt_pos.mpr hC
  rw [one_div,mul_comm,← div_eq_mul_inv]
  exact (div_le_iff₀ hp).mpr (by simpa [mul_comm] using hsqrt)

 theorem original_phase_magnitude (d : LocalBranchData) :
    ∃ c C r : ℝ, 0 < c ∧ 0 < C ∧ 0 < r ∧ ∀ ε u : ℝ,
      0 < ε → ε < r → |u| < r →
      c*Real.sqrt (|u|+ε) ≤ ‖originalPhase d ε u‖ ∧
        ‖originalPhase d ε u‖ ≤ C*Real.sqrt (|u|+ε) := by
  obtain ⟨cD,CD,rD,hcD,hCD,hrD,hD⟩ := current_modulus_Q d
  obtain ⟨cφ,rφ,hcφ,hrφ,hφ⟩ := lowerArccos_norm_lower
  let r := min rD (min (rφ/(4*CD)) (1/(400*CD)))
  have hr : 0 < r := by dsimp [r]; positivity
  have hrs : r ≤ rD ∧ r ≤ rφ/(4*CD) ∧ r ≤ 1/(400*CD) := by
    have he : r ≤ min rD (min (rφ/(4*CD)) (1/(400*CD))) := le_rfl
    simpa only [le_min_iff] using he
  refine ⟨cφ*Real.sqrt cD,6*Real.sqrt CD,r,by positivity,by positivity,hr,?_⟩
  intro ε u hε hεr hur
  obtain ⟨hlo,hhi⟩ := hD ε 0 u hε (hεr.trans_le hrs.1) le_rfl hrD (hur.trans_le hrs.1)
  simp only [mul_zero,add_zero] at hlo hhi
  have hsmall : ‖currentD d ε 0 u‖ < rφ := by
    have hh := (le_div_iff₀ (show 0 < 4*CD by positivity)).mp hrs.2.1
    nlinarith
  have hsmall' : ‖currentD d ε 0 u‖ ≤ 1/100 := by
    have hh := (le_div_iff₀ (show 0 < 400*CD by positivity)).mp hrs.2.2
    nlinarith
  have hl := hφ (currentW d ε 0 u) hsmall
  have hu := lowerArccos_norm_upper (currentW d ε 0 u) hsmall'
  have hslo := Real.sqrt_le_sqrt hlo
  have hshi := Real.sqrt_le_sqrt hhi
  rw [Real.sqrt_mul hcD.le] at hslo
  rw [Real.sqrt_mul hCD.le] at hshi
  simp only [currentD] at hslo hshi
  constructor
  · change cφ*Real.sqrt cD*Real.sqrt (|u|+ε) ≤ ‖lowerArccos (currentW d ε 0 u)‖
    have hh := mul_le_mul_of_nonneg_left hslo hcφ.le
    nlinarith
  · change ‖lowerArccos (currentW d ε 0 u)‖ ≤ 6*Real.sqrt CD*Real.sqrt (|u|+ε)
    nlinarith

end
end IsingBulk.Tail
