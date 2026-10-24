import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section

/-- Algebraic splitting of an already proved complex norm envelope. No phase
alignment or positivity of the complex coefficient is used. -/
theorem complex_error_split {z : ℂ} {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hz : ‖z‖≤A+B) : ∃u v : ℂ,z=u+v ∧ ‖u‖≤A ∧ ‖v‖≤B := by
  by_cases h : A+B=0
  · have hz0 : z=0 := norm_eq_zero.mp (le_antisymm (by simpa only [h] using hz) (norm_nonneg _))
    exact ⟨0,0,by simp only [hz0,add_zero],by simpa only [norm_zero] using hA,by simpa only [norm_zero] using hB⟩
  have hp : 0<A+B := lt_of_le_of_ne (add_nonneg hA hB) (Ne.symm h)
  refine ⟨((A/(A+B):ℝ):ℂ)*z,((B/(A+B):ℝ):ℂ)*z,?_,?_,?_⟩
  · rw [←add_mul,←Complex.ofReal_add,←add_div,div_self h,Complex.ofReal_one,one_mul]
  · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (div_nonneg hA hp.le)]
    have hh := mul_le_mul_of_nonneg_left hz (div_nonneg hA hp.le)
    simpa only [div_mul_cancel₀ _ h] using hh
  · rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (div_nonneg hB hp.le)]
    have hh := mul_le_mul_of_nonneg_left hz (div_nonneg hB hp.le)
    simpa only [div_mul_cancel₀ _ h] using hh

end
end IsingBulk.Anisotropic.NegativeDominance
