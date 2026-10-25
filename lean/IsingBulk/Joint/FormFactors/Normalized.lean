import IsingBulk.Joint.FormFactors.ComplexContours
import IsingBulk.Joint.Geometry.Modulus
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Explicit single-valued physical fourth-root branches and literal complete
odd/even JOINT susceptibilities. No analytic-continuation existence predicate is used. -/
namespace IsingBulk.Joint.FormFactors
noncomputable section

def fourthRoot (v : ℂ) : ℂ := Complex.exp ((1/4:ℂ) * Complex.log v)
def highPrefactor (K : Coupling) : ℂ := fourthRoot (1-p K^2)
def lowPrefactor (K : Coupling) : ℂ := fourthRoot (1-(p K)⁻¹^2)

/-- JOINT (3.10), containing every positive odd particle number once. -/
def highNormalizedBulk (K : Coupling) : ℂ :=
  highPrefactor K * ∑' n : ℕ, p K^n * unscaledFullCoefficient (2*n+1) K

/-- JOINT (3.11), all positive even numbers, with the zero-particle vacuum removed. -/
def lowNormalizedBulk (K : Coupling) : ℂ :=
  lowPrefactor K * ∑' n : ℕ, p K^(n+1) * unscaledFullCoefficient (2*n+2) K

theorem fourthRoot_pow_four {v : ℂ} (hv : v ≠ 0) : fourthRoot v^4=v := by
  unfold fourthRoot
  rw [← Complex.exp_nat_mul]
  convert Complex.exp_log hv using 1
  congr 1
  ring

theorem fourthRoot_ne_zero (v : ℂ) : fourthRoot v ≠ 0 := Complex.exp_ne_zero _

theorem fourthRoot_analyticAt {v : ℂ} (hv : v ∈ Complex.slitPlane) :
    AnalyticAt ℂ fourthRoot v :=
  analyticAt_cexp.comp (analyticAt_const.mul (analyticAt_clog hv))

theorem one_sub_sq_mem_slitPlane {v : ℂ} (hv : ‖v‖ < 1) :
    1-v^2 ∈ Complex.slitPlane := by
  rw [sub_eq_add_neg]
  apply Complex.mem_slitPlane_of_norm_lt_one
  simpa only [norm_neg,norm_pow] using
    pow_lt_one₀ (norm_nonneg v) hv (by decide : 2 ≠ 0)

theorem p_analyticAt_normalized (K : Coupling) : AnalyticAt ℂ p K :=
  (Complex.analyticAt_sinh.comp analyticAt_fst).mul
    (Complex.analyticAt_sinh.comp analyticAt_snd)

theorem highPrefactor_analyticOnNhd : AnalyticOnNhd ℂ highPrefactor highDomain := by
  intro K hK
  exact (fourthRoot_analyticAt (one_sub_sq_mem_slitPlane (norm_p_lt_one hK))).comp (f := fun K => 1-p K^2)
    (analyticAt_const.sub ((p_analyticAt_normalized K).pow 2))

theorem lowPrefactor_analyticOnNhd : AnalyticOnNhd ℂ lowPrefactor lowDomain := by
  intro K hK
  have hp : 1 < ‖p K‖ := one_lt_norm_p hK
  have hp0 : p K ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans hp)
  have hpi : ‖(p K)⁻¹‖ < 1 := by rw [norm_inv]; exact (inv_lt_one₀ (zero_lt_one.trans hp)).mpr hp
  exact (fourthRoot_analyticAt (one_sub_sq_mem_slitPlane hpi)).comp (f := fun K => 1-(p K)⁻¹^2)
    (analyticAt_const.sub (((p_analyticAt_normalized K).inv hp0).pow 2))

theorem highPrefactor_pow_four {K : Coupling} (hK : K ∈ highDomain) :
    highPrefactor K^4 = 1-p K^2 :=
  fourthRoot_pow_four (Complex.slitPlane_ne_zero (one_sub_sq_mem_slitPlane (norm_p_lt_one hK)))

theorem lowPrefactor_pow_four {K : Coupling} (hK : K ∈ lowDomain) :
    lowPrefactor K^4 = 1-(p K)⁻¹^2 := by
  have hp := one_lt_norm_p hK
  apply fourthRoot_pow_four
  apply Complex.slitPlane_ne_zero
  apply one_sub_sq_mem_slitPlane
  rw [norm_inv]
  exact (inv_lt_one₀ (zero_lt_one.trans hp)).mpr hp

theorem fourthRoot_real {a : ℝ} (ha : 0 < a) :
    fourthRoot (a:ℂ) = ((a^(1/4:ℝ):ℝ):ℂ) := by
  rw [fourthRoot,Real.rpow_def_of_pos ha,← Complex.ofReal_log ha.le,Complex.ofReal_exp]
  congr 1
  push_cast
  ring

theorem fourthRoot_real_positive {a : ℝ} (ha : 0 < a) :
    (fourthRoot (a:ℂ)).im = 0 ∧ 0 < (fourthRoot (a:ℂ)).re := by
  rw [fourthRoot_real ha]
  exact ⟨rfl,Real.rpow_pos_of_pos ha _⟩

@[simp] theorem highPrefactor_zero : highPrefactor (0,0) = 1 := by
  simp [highPrefactor,fourthRoot,p,S,T]

theorem highPrefactor_ne_zero (K : Coupling) : highPrefactor K ≠ 0 := fourthRoot_ne_zero _
theorem lowPrefactor_ne_zero (K : Coupling) : lowPrefactor K ≠ 0 := fourthRoot_ne_zero _
end
end IsingBulk.Joint.FormFactors
