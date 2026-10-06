import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! Quantitative arithmetic in prop:F. Mixed compact/branch inflation is
retained and paid by half of the compact quadratic penalty. -/
namespace IsingBulk.Tail
noncomputable section

 theorem mixed_inflation_absorption {a C N M : ℝ} (ha : 0 < a) (hN : 0 ≤ N) :
    C*M*Real.sqrt N ≤ (a/2)*M^2+C^2*N/(2*a) := by
  have hs := sq_nonneg (a*M-C*Real.sqrt N)
  have hsq := Real.sq_sqrt hN
  apply (mul_le_mul_iff_left₀ (show 0 < 2*a by positivity)).mp
  have he : ((a/2)*M^2+C^2*N/(2*a))*(2*a) = a^2*M^2+C^2*N := by
    field_simp
  rw [he]
  nlinarith

 theorem selected_pair_penalty {a C N M : ℝ} (ha : 0 < a) (hN : 0 ≤ N) :
    Real.exp (C*N+C*M*Real.sqrt N-a*M^2) ≤
      Real.exp ((C+C^2/(2*a))*N)*Real.exp (-(a/2)*M^2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hh := mixed_inflation_absorption (C := C) (M := M) ha hN
  convert add_le_add_right hh (C*N-a*M^2) using 1 <;> ring

 theorem gaussian_linear_completion {a x M : ℝ} (ha : 0 < a) :
    M*x-a*M^2 ≤ x^2/(4*a) := by
  apply (le_div_iff₀ (show 0 < 4*a by positivity)).mpr
  nlinarith [sq_nonneg (2*a*M-x)]

 theorem compact_assignment_penalty {a X : ℝ} (ha : 0 < a) (hX : 0 < X) (M : ℕ) :
    X^M*Real.exp (-a*(M:ℝ)^2) ≤ Real.exp ((Real.log X)^2/(4*a)) := by
  rw [← Real.exp_log hX, ← Real.exp_nat_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simpa [sub_eq_add_neg] using gaussian_linear_completion (M := (M:ℝ)) (x := Real.log X) ha

end
end IsingBulk.Tail
