import IsingBulk.Anisotropic.NegativeNormalForm.HessianBounds
import IsingBulk.Anisotropic.NegativeDominance.ModelOrderInterface
import Mathlib.Analysis.SpecificLimits.Basic

/-! Uniform particle-index consequences of the actual scalar Hessian bounds. -/
namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Filter
open scoped Topology
open IsingBulk.Anisotropic.NegativeNormalForm

theorem winding_angle_tendsto_zero :
    Tendsto (fun n : ℕ => Real.pi / (n : ℝ)) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop

theorem winding_angle_complex_tendsto_zero :
    Tendsto (fun n : ℕ => ((Real.pi / (n : ℝ) : ℝ) : ℂ)) atTop (𝓝 0) := by
  simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto 0).comp winding_angle_tendsto_zero

theorem tau_tendsto_zero : Tendsto tau atTop (𝓝 0) := by
  have hh := (tendsto_const_nhds (x := (1 : ℝ))).sub (Real.continuous_cos.tendsto 0 |>.comp winding_angle_tendsto_zero)
  change Tendsto (fun n : ℕ => 1 - Real.cos (Real.pi / n)) atTop (𝓝 0)
  simpa [Function.comp_def] using hh

theorem tau_complex_tendsto_zero :
    Tendsto (fun n : ℕ => (tau n : ℂ)) atTop (𝓝 0) := by
  simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto 0).comp tau_tendsto_zero

/-- A single C works for all sufficiently large particle indices. -/
theorem hessianFactor_eventually_quadratic (B : ℂ → ℂ) (phi : ℝ)
    (hB : AnalyticAt ℂ B 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ‖hessianFactor (B (tau n)) (Real.cos phi) (Real.sin phi) n - 1‖ ≤
        C / (n : ℝ)^2 := by
  obtain ⟨C, hC, hb⟩ := centralHessian_quadratic_bound B phi hB
  refine ⟨C * Real.pi^2, mul_pos hC (sq_pos_of_pos Real.pi_pos), ?_⟩
  filter_upwards [winding_angle_complex_tendsto_zero.eventually hb] with n hn
  rw [centralHessian_at_winding] at hn
  simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow, mul_div_assoc] using hn

theorem hessianFactor_eventually_nonzero (B : ℂ → ℂ) (phi : ℝ)
    (hB : AnalyticAt ℂ B 0) :
    ∀ᶠ n : ℕ in atTop, hessianFactor (B (tau n)) (Real.cos phi) (Real.sin phi) n ≠ 0 := by
  have hh := winding_angle_complex_tendsto_zero.eventually
    (centralHessian_eventually_nonzero B phi hB)
  simpa only [centralHessian_at_winding] using hh

/-- Physical B values and the actual Hessian are nonzero at all sufficiently
large n. No common phase across n is imposed. -/
theorem physical_prefactor_eventually_nonzero (B rootB : ℂ → ℂ) (phi : ℝ)
    (hB : AnalyticAt ℂ B 0) (hB0 : B 0 ≠ 0)
    (hroot : ContinuousAt rootB 0) (hroot0 : rootB 0 ≠ 0)
    (hphi : Real.sin phi ≠ 0) :
    ∀ᶠ n : ℕ in atTop, modelPrefactor (B (tau n)) (rootB (tau n))
      (hessianFactor (B (tau n)) (Real.cos phi) (Real.sin phi) n) (Real.sin phi) n ≠ 0 := by
  have hb := tau_complex_tendsto_zero.eventually (hB.continuousAt.eventually_ne hB0)
  have hr := tau_complex_tendsto_zero.eventually (hroot.eventually_ne hroot0)
  filter_upwards [hb, hr, hessianFactor_eventually_nonzero B phi hB,
    eventually_ge_atTop (1 : ℕ)] with n hnB hnroot hnh hnp
  exact modelPrefactor_ne_zero _ _ _ _ n hnB hnroot hnh hphi (by omega)

end
end IsingBulk.Anisotropic.NegativeDominance
