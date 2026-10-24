import IsingBulk.Tail.GlobalAnalytic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic

/-! The genuine all-index scalar summability step behind ANISO (5.7)--(5.8).
The angular/parameter estimates are not assumed to be physical interfaces. -/
namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Filter Asymptotics
open scoped Topology

/-- The `n log(n+1)` entropy term is eventually absorbed into half the
quadratic decay, with a fixed coefficient chosen before the particle limit. -/
theorem entropy_eventually_le_half_quadratic {kappa : ℝ} (hk : 0 < kappa) (C : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      C * n * Real.log ((n : ℝ) + 1) ≤ kappa / 2 * (n : ℝ)^2 := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hl := (Real.isLittleO_log_id_atTop.const_mul_left C).comp_tendsto ht
  filter_upwards [hl.bound (show 0 < kappa / 4 by positivity),
    eventually_ge_atTop (1 : ℕ)] with n hlog hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  simp only [Real.norm_eq_abs, Function.comp_apply, id_eq] at hlog
  rw [abs_of_nonneg (show (0 : ℝ) ≤ n + 1 by positivity)] at hlog
  have hle := le_trans (le_abs_self (C * Real.log ((n : ℝ) + 1))) hlog
  have hle' : C * Real.log ((n : ℝ) + 1) ≤ kappa / 2 * n :=
    le_trans hle (by nlinarith)
  have hmul := mul_le_mul_of_nonneg_left hle' (show (0 : ℝ) ≤ n by positivity)
  nlinarith

/-- Polynomially weighted matched-Pfaffian envelopes are summable over
all particle indices, for every fixed derivative order. -/
theorem summable_polynomial_entropy_gaussian {kappa : ℝ} (hk : 0 < kappa)
    (C : ℝ) (m : ℕ) :
    Summable (fun n : ℕ => (n : ℝ)^m *
      Real.exp (-kappa * (n : ℝ)^2 + C * n * Real.log ((n : ℝ) + 1) + C)) := by
  have hs := (IsingBulk.Tail.summable_polynomial_gaussian 0
    (show 0 < kappa / 2 by positivity) m).mul_left (Real.exp C)
  apply hs.of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [entropy_eventually_le_half_quadratic hk C] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (n : ℝ)^m * Real.exp (C + (0 * n - kappa / 2 * (n : ℝ)^2)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      nlinarith
    _ = Real.exp C * ((n : ℝ)^m * Real.exp (0 * n - kappa / 2 * (n : ℝ)^2)) := by
      rw [Real.exp_add]
      ring

end
end IsingBulk.Anisotropic.NegativeDominance
