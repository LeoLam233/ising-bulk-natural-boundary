import IsingBulk.Anisotropic.NegativeDominance.ExactConcavity
import IsingBulk.Anisotropic.NegativeDominance.GammaCoarseBounds

/-! Actual scalar-branch hypotheses imply uniform exact-model concavity.
No dominance or concavity estimate is assumed here. -/
namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Filter
open scoped Topology

def physicalModel (B rootB : ℂ → ℂ) (phi : ℝ) (n j : ℕ) : ℂ :=
  model (B (tau n)) (rootB (tau n))
    (hessianFactor (B (tau n)) (Real.cos phi) (Real.sin phi) n) (Real.sin phi) n j

theorem physical_model_second_difference_upper
    (B rootB : ℂ → ℂ) (phi : ℝ) (hB : AnalyticAt ℂ B 0) (hB0 : B 0 ≠ 0)
    (hroot : ContinuousAt rootB 0) (hroot0 : rootB 0 ≠ 0)
    (hsq : ∀ᶠ t in 𝓝 (0 : ℂ), rootB t ^ 2 = B t) (hphi : Real.sin phi ≠ 0)
    (p : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N, Odd n → ∀ j : ℕ,
      2 * alpha (n + 4 * p) ≤ j →
      Real.log ‖physicalModel B rootB phi (n + 4 * p) j‖ -
        2 * Real.log ‖physicalModel B rootB phi (n + 2 * p) j‖ +
        Real.log ‖physicalModel B rootB phi n j‖ ≤
        -((2 * p : ℕ) : ℝ)^2 * Real.log j +
          ((2 * p : ℕ) : ℝ)^2 * modelQuadraticConstant (B 0) (Real.sin phi) +
          2 * ((2 * p : ℕ) : ℝ)^3 + 4 * C + 4 * ((2 * p : ℕ) : ℝ)^2 := by
  obtain ⟨C, hC, he⟩ := physical_modelAnalyticError_eventually_bounded B phi hB hB0
  have hb := tau_complex_tendsto_zero.eventually (hB.continuousAt.eventually_ne hB0)
  have hr := tau_complex_tendsto_zero.eventually (hroot.eventually_ne hroot0)
  have hh := hessianFactor_eventually_nonzero B phi hB
  have hsqn := tau_complex_tendsto_zero.eventually hsq
  have hall := hb.and (hr.and (hh.and (hsqn.and he)))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hall
  refine ⟨C, hC, max N 4, ?_⟩
  intro n hn ho j hj
  have hn4 : 4 ≤ n := le_trans (le_max_right _ _) hn
  have hA : 0 < alpha (n + 4 * p) := by
    have ht : 4 ≤ n + 4 * p := by omega
    have ht2 : 16 ≤ (n + 4 * p) * (n + 4 * p) := by nlinarith
    unfold alpha
    omega
  have hj' : alpha (n + 4 * p) < j := by omega
  have hbound := model_log_second_difference_upper
    (fun k => B (tau k)) (fun k => rootB (tau k))
    (fun k => hessianFactor (B (tau k)) (Real.cos phi) (Real.sin phi) k)
    (B 0) (Real.sin phi) C n p j hn4 ho hj' hphi
    (fun k hk _ => by
      have ht := hN k (le_trans (le_max_left _ _) (hn.trans hk))
      exact ⟨ht.1, ht.2.1, ht.2.2.1, ht.2.2.2.1⟩)
    (fun k hk hok => (hN k (le_trans (le_max_left _ _) (hn.trans hk))).2.2.2.2 hok)
  have hg := gamma_alpha_error_le_step_square n p j (by omega) ho hj
  change _ ≤ _ at hbound
  unfold physicalModel
  linarith

/-- Uniform strict concavity of the actual first-winding model on every
sufficiently large odd index with 2α_(n+4p)≤j. This includes the manuscript's
entire intermediate window for large j, not only a fixed relative window. -/
theorem physical_model_strict_concavity
    (B rootB : ℂ → ℂ) (phi : ℝ) (hB : AnalyticAt ℂ B 0) (hB0 : B 0 ≠ 0)
    (hroot : ContinuousAt rootB 0) (hroot0 : rootB 0 ≠ 0)
    (hsq : ∀ᶠ t in 𝓝 (0 : ℂ), rootB t ^ 2 = B t) (hphi : Real.sin phi ≠ 0)
    (p : ℕ) (hp : 0 < p) :
    ∃ N J : ℕ, ∀ n ≥ N, Odd n → ∀ j ≥ J,
      2 * alpha (n + 4 * p) ≤ j →
      Real.log ‖physicalModel B rootB phi (n + 4 * p) j‖ -
        2 * Real.log ‖physicalModel B rootB phi (n + 2 * p) j‖ +
        Real.log ‖physicalModel B rootB phi n j‖ ≤
        -(((2 * p : ℕ) : ℝ)^2 / 2) * Real.log j := by
  obtain ⟨C, hC, N, hN⟩ := physical_model_second_difference_upper B rootB phi hB hB0
    hroot hroot0 hsq hphi p
  let D : ℝ := ((2 * p : ℕ) : ℝ)
  let q := modelQuadraticConstant (B 0) (Real.sin phi)
  let K := |q| + 2 * D + 4 * C + 4
  have ht : Tendsto (fun j : ℕ => Real.log (j : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop (2 * K)))
  refine ⟨N, J, ?_⟩
  intro n hn ho j hj hja
  have hb := hN n hn ho j hja
  have hlog := hJ j hj
  have hD : 1 ≤ D := by dsimp [D]; exact_mod_cast (by omega : 1 ≤ 2 * p)
  have hD2 : 1 ≤ D^2 := by nlinarith
  have hq := mul_nonneg (sq_nonneg D) (sub_nonneg.mpr (le_abs_self q))
  have hce := mul_nonneg (show 0 ≤ 4 * C by positivity) (sub_nonneg.mpr hD2)
  have hle := mul_nonneg (sq_nonneg D) (sub_nonneg.mpr hlog)
  change _ ≤ - (D^2 / 2) * Real.log j
  change _ ≤ -D^2 * Real.log j + D^2 * q + 2 * D^3 + 4 * C + 4 * D^2 at hb
  dsimp [K] at hle
  nlinarith

end
end IsingBulk.Anisotropic.NegativeDominance
