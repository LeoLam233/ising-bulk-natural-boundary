import IsingBulk.Anisotropic.NegativeDominance.PhysicalSequences

/-! Quantitative logarithmic control of the actual Hessian factor. -/
namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Filter
open scoped Topology
open IsingBulk.Anisotropic.NegativeNormalForm

theorem abs_log_le_two_mul_abs_sub_one {x : ℝ} (hx : 1 / 2 ≤ x) :
    |Real.log x| ≤ 2 * |x - 1| := by
  have hpos : 0 < x := by linarith
  have hu := Real.log_le_sub_one_of_pos hpos
  have hl := Real.one_sub_inv_le_log_of_pos hpos
  have habs : 0 ≤ |x - 1| := abs_nonneg _
  have hupper : Real.log x ≤ 2 * |x - 1| := by linarith [le_abs_self (x - 1)]
  have hratio : (1 - x) / x ≤ 2 * |x - 1| := by
    apply (div_le_iff₀ hpos).mpr
    nlinarith [neg_le_abs (x - 1), mul_nonneg habs (show 0 ≤ x - 1 / 2 by linarith)]
  have he : x⁻¹ - 1 = (1 - x) / x := by field_simp
  apply abs_le.mpr
  constructor <;> linarith

theorem hessianFactor_tendsto_one (B : ℂ → ℂ) (phi : ℝ)
    (hB : AnalyticAt ℂ B 0) :
    Tendsto (fun n : ℕ => hessianFactor (B (tau n)) (Real.cos phi) (Real.sin phi) n)
      atTop (𝓝 1) := by
  have hh := (centralHessian_analyticAt_zero B phi hB).continuousAt.tendsto.comp
    winding_angle_complex_tendsto_zero
  simpa only [Function.comp_def, centralHessian_at_winding, centralHessian_zero] using hh

/-- The complex Hessian contributes only a dimension-uniform O(n⁻²)
logarithmic perturbation, proved from scalar holomorphy. -/
theorem hessianFactor_log_norm_bound (B : ℂ → ℂ) (phi : ℝ)
    (hB : AnalyticAt ℂ B 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      |Real.log ‖hessianFactor (B (tau n)) (Real.cos phi) (Real.sin phi) n‖| ≤ C / (n : ℝ)^2 := by
  obtain ⟨C, hC, hb⟩ := hessianFactor_eventually_quadratic B phi hB
  have ht := (hessianFactor_tendsto_one B phi hB).norm
  have hhalf : ∀ᶠ n : ℕ in atTop,
      1 / 2 ≤ ‖hessianFactor (B (tau n)) (Real.cos phi) (Real.sin phi) n‖ := by
    apply (ht.eventually (eventually_gt_nhds (show (1 / 2 : ℝ) < ‖(1 : ℂ)‖ by norm_num))).mono
    intro n hn
    exact hn.le
  refine ⟨2 * C, by positivity, ?_⟩
  filter_upwards [hb, hhalf] with n hn hh
  calc
    _ ≤ 2 * |‖hessianFactor (B (tau n)) (Real.cos phi) (Real.sin phi) n‖ - 1| :=
      abs_log_le_two_mul_abs_sub_one hh
    _ ≤ 2 * ‖hessianFactor (B (tau n)) (Real.cos phi) (Real.sin phi) n - 1‖ := by
      gcongr
      simpa using abs_norm_sub_norm_le
        (hessianFactor (B (tau n)) (Real.cos phi) (Real.sin phi) n) (1 : ℂ)
    _ ≤ 2 * (C / (n : ℝ)^2) := mul_le_mul_of_nonneg_left hn (by norm_num)
    _ = _ := by ring

end
end IsingBulk.Anisotropic.NegativeDominance
