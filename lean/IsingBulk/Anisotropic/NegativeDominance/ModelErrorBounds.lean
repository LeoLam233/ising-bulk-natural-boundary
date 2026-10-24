import IsingBulk.Anisotropic.NegativeDominance.ModelDecomposition
import IsingBulk.Anisotropic.NegativeDominance.AnalyticFactorBounds
import IsingBulk.Anisotropic.NegativeDominance.TauLogarithm

/-! A proved uniform bound on the complete analytic correction in the exact
model logarithm. The constant is chosen before n and j. -/
namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Filter
open scoped Topology

theorem modelAnalyticError_bound (B0 Bn hn : ℂ) (n : ℕ) (hnpos : 0 < n) (hnodd : Odd n)
    (CB CH CT : ℝ)
    (hB : |Real.log ‖Bn‖ - Real.log ‖B0‖| ≤ CB / (n : ℝ)^2)
    (hH : |Real.log ‖hn‖| ≤ CH / (n : ℝ)^2)
    (hT : |Real.log (Real.pi^2 / 2) - 2 * Real.log n - Real.log (tau n)| ≤ CT / (n : ℝ)^2) :
    |modelAnalyticError B0 Bn hn n| ≤ CB + CH + CT := by
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
  have hnz : (n : ℝ) ≠ 0 := by linarith
  have ha := two_mul_alpha_add_one n hnodd
  have har : 2 * (alpha n : ℝ) + 1 = (n : ℝ)^2 := by exact_mod_cast (ha.trans (pow_two n).symm)
  have hsq : (1 : ℝ) ≤ (n : ℝ)^2 := by nlinarith
  have hap : 0 ≤ (alpha n : ℝ) := Nat.cast_nonneg _
  have h1 : |(alpha n : ℝ) - 1 / 2| ≤ (n : ℝ)^2 := by rw [abs_le]; constructor <;> nlinarith
  have h2 : |(alpha n : ℝ)| ≤ (n : ℝ)^2 := by rw [abs_of_nonneg hap]; nlinarith
  have h3 : |(alpha n : ℝ) - 1| ≤ (n : ℝ)^2 := by rw [abs_le]; constructor <;> nlinarith
  have aux (a u C : ℝ) (ha : |a| ≤ (n : ℝ)^2) (hu : |u| ≤ C / (n : ℝ)^2) : |a * u| ≤ C := by
    rw [abs_mul]
    calc
      _ ≤ (n : ℝ)^2 * (C / (n : ℝ)^2) :=
        mul_le_mul ha hu (abs_nonneg _) (by positivity)
      _ = C := by field_simp
  have hb := aux _ _ _ h1 hB
  have hh := aux _ _ _ h2 hH
  have ht := aux _ _ _ h3 hT
  let A := ((alpha n : ℝ) - 1 / 2) * (Real.log ‖Bn‖ - Real.log ‖B0‖)
  let D := (alpha n : ℝ) * Real.log ‖hn‖
  let T := ((alpha n : ℝ) - 1) * (Real.log (Real.pi^2 / 2) - 2 * Real.log n - Real.log (tau n))
  change |A - D - T| ≤ CB + CH + CT
  calc
    _ ≤ |A - D| + |T| := abs_sub _ _
    _ ≤ (|A| + |D|) + |T| := by linarith [abs_sub A D]
    _ ≤ _ := add_le_add (add_le_add hb hh) ht

/-- Actual analytic B and actual Hessian yield one bounded error for all
sufficiently large odd particle indices. No coefficient estimate is assumed. -/
theorem physical_modelAnalyticError_eventually_bounded (B : ℂ → ℂ) (phi : ℝ)
    (hB : AnalyticAt ℂ B 0) (hB0 : B 0 ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, Odd n →
      |modelAnalyticError (B 0) (B (tau n))
        (hessianFactor (B (tau n)) (Real.cos phi) (Real.sin phi) n) n| ≤ C := by
  obtain ⟨CB, hCB, hb⟩ := physical_B_log_norm_bound B hB hB0
  obtain ⟨CH, hCH, hh⟩ := hessianFactor_log_norm_bound B phi hB
  refine ⟨CB + CH + Real.pi^2 / 10, by positivity, ?_⟩
  filter_upwards [hb, hh, eventually_ge_atTop (2 : ℕ)] with n hnB hnH hn hnodd
  apply modelAnalyticError_bound _ _ _ n (by omega) hnodd CB CH (Real.pi^2 / 10) hnB hnH
  have ht := log_tau_error_bounds n hn
  rw [abs_of_nonneg ht.1]
  convert ht.2 using 1
  ring

end
end IsingBulk.Anisotropic.NegativeDominance
