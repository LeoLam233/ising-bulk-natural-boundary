import IsingBulk.Anisotropic.NegativeDominance.LogNormBounds

/-! Dimension-uniform bounds for the actual analytic scalar B in the model. -/
namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Filter
open scoped Topology
open IsingBulk.Anisotropic.NegativeNormalForm

theorem analytic_locally_linear_bound {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ z in 𝓝 (0 : ℂ), ‖f z - f 0‖ ≤ C * ‖z‖ := by
  let G := dslope f 0
  have hG : AnalyticAt ℂ G 0 := analyticAt_dslope_center hf
  have hb := hG.continuousAt.norm.eventually_lt continuousAt_const
    (show ‖G 0‖ < ‖G 0‖ + 1 by linarith)
  refine ⟨‖G 0‖ + 1, by positivity, ?_⟩
  filter_upwards [hb] with z hz
  have he := sub_smul_dslope f 0 z
  simp only [sub_zero, smul_eq_mul] at he
  rw [← he, norm_mul]
  dsimp [G] at hz
  nlinarith [norm_nonneg z]

theorem log_norm_difference_le {x y : ℂ} (hy : y ≠ 0) (hhalf : ‖y‖ / 2 ≤ ‖x‖) :
    |Real.log ‖x‖ - Real.log ‖y‖| ≤ (2 / ‖y‖) * ‖x - y‖ := by
  have hyp : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hxp : 0 < ‖x‖ := by linarith
  rw [← Real.log_div hxp.ne' hyp.ne']
  have hhalf' : 1 / 2 ≤ ‖x‖ / ‖y‖ := by apply (le_div_iff₀ hyp).mpr; linarith
  calc
    _ ≤ 2 * |‖x‖ / ‖y‖ - 1| := abs_log_le_two_mul_abs_sub_one hhalf'
    _ = (2 / ‖y‖) * |‖x‖ - ‖y‖| := by
      rw [div_sub_one hyp.ne', abs_div, abs_of_pos hyp]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (abs_norm_sub_norm_le x y) (by positivity)

/-- The constant is independent of n and j. This is the actual analytic B,
not a freely chosen sequence of model constants. -/
theorem physical_B_log_norm_bound (B : ℂ → ℂ)
    (hB : AnalyticAt ℂ B 0) (hB0 : B 0 ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      |Real.log ‖B (tau n)‖ - Real.log ‖B 0‖| ≤ C / (n : ℝ)^2 := by
  obtain ⟨C, hC, hb⟩ := analytic_locally_linear_bound hB
  have hyp : 0 < ‖B 0‖ := norm_pos_iff.mpr hB0
  have ht := (hB.continuousAt.tendsto.comp tau_complex_tendsto_zero).norm
  have hhalf : ∀ᶠ n : ℕ in atTop, ‖B 0‖ / 2 ≤ ‖B (tau n)‖ := by
    apply (ht.eventually (eventually_gt_nhds (show ‖B 0‖ / 2 < ‖B 0‖ by linarith))).mono
    intro n hn
    exact hn.le
  refine ⟨C * Real.pi^2 / ‖B 0‖, by positivity, ?_⟩
  filter_upwards [tau_complex_tendsto_zero.eventually hb, hhalf,
    eventually_ge_atTop (1 : ℕ)] with n hn hh hnp
  have hnpos : 0 < n := by omega
  have htau := tau_bounds n hnpos
  have htaup := tau_pos n hnpos
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos htaup] at hn
  calc
    _ ≤ (2 / ‖B 0‖) * ‖B (tau n) - B 0‖ := log_norm_difference_le hB0 hh
    _ ≤ (2 / ‖B 0‖) * (C * tau n) := mul_le_mul_of_nonneg_left hn (by positivity)
    _ ≤ (2 / ‖B 0‖) * (C * (Real.pi^2 / (2 * (n : ℝ)^2))) := by gcongr; exact htau.2
    _ = _ := by ring

end
end IsingBulk.Anisotropic.NegativeDominance
