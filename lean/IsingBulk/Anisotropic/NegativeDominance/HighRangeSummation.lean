import IsingBulk.Anisotropic.NegativeDominance.HighRangeCalculus
import Mathlib.Analysis.SpecificLimits.Normed

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open scoped BigOperators

/-- The genuine growing high range, with its manuscript cutoff. -/
def highRangePart (j : ℝ) (f : ℕ→ℂ) (N : ℕ) : ℂ :=
  if 1≤N ∧ j/Real.sqrt (Real.log j)≤(N : ℝ)^2 then f N else 0

/-- The complete infinite high-index sum, not a finite-index surrogate,
is controlled by one summable geometric envelope. -/
theorem high_range_summable_bound (j C : ℝ) (hj : 0<j)
    (hL : 1024≤Real.log j) (hC : 32*C≤Real.log j) (f : ℕ→ℂ)
    (hf : ∀N : ℕ,1≤N → j/Real.sqrt (Real.log j)≤(N : ℝ)^2 →
      ‖f N‖≤Real.exp (2*j*Real.log N-(N : ℝ)^2/2*Real.log N+C*(N : ℝ)^2)) :
    Summable (highRangePart j f) ∧
    ∑'N,‖highRangePart j f N‖≤
      Real.exp (j*Real.log j-j*Real.sqrt (Real.log j)/32)/(1-Real.exp (-1)) := by
  let A := Real.exp (j*Real.log j-j*Real.sqrt (Real.log j)/32)
  have hA : 0≤A := (Real.exp_pos _).le
  have hr : |Real.exp (-1)|<1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by norm_num)
  have hgeo := (summable_geometric_of_abs_lt_one hr).mul_left A
  have hbound (N : ℕ) : ‖highRangePart j f N‖≤A*Real.exp (-1)^N := by
    by_cases hh : 1≤N ∧ j/Real.sqrt (Real.log j)≤(N : ℝ)^2
    · rw [highRangePart,ite_eq_left hh]
      have he := high_range_exponent_bound j (N : ℝ) C hj (by exact_mod_cast hh.1) hL hC hh.2
      have hb := (hf N hh.1 hh.2).trans (Real.exp_le_exp.mpr he)
      have hex : Real.exp (j*Real.log j-j*Real.sqrt (Real.log j)/32-(N : ℝ))=A*Real.exp (-1)^N := by
        rw [sub_eq_add_neg,Real.exp_add]
        congr 1
        rw [←Real.exp_nat_mul]
        congr 1
        ring
      simpa only [hex] using hb
    · simp only [highRangePart,ite_eq_right hh,norm_zero]
      positivity
  have hsNorm : Summable (fun N => ‖highRangePart j f N‖) :=
    Summable.of_nonneg_of_le (fun N => norm_nonneg _) hbound hgeo
  refine ⟨hsNorm.of_norm,?_⟩
  have ht := hsNorm.tsum_le_tsum hbound hgeo
  rw [tsum_mul_left,tsum_geometric_of_abs_lt_one hr] at ht
  simpa only [A,div_eq_mul_inv] using ht

end
end IsingBulk.Anisotropic.NegativeDominance
