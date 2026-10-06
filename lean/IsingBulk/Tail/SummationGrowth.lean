import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! Scalar comparisons used only after differentiation and actual sector
estimates. Constants are fixed before the radial limit. -/
namespace IsingBulk.Tail
noncomputable section
open Filter Asymptotics
open scoped Topology

theorem exp_sublinear_isLittleO {f : ℝ → ℝ} (hf : f =o[atTop] (fun H : ℝ => H))
    {c : ℝ} (hc : 0 < c) :
    (fun H => Real.exp (f H)) =o[atTop] (fun H => Real.exp (c*H)) := by
  apply Real.isLittleO_exp_comp_exp_comp.mpr
  apply tendsto_atTop_mono' atTop _ (tendsto_id.const_mul_atTop (show 0 < c/2 by positivity))
  filter_upwards [hf.bound (show 0 < c/2 by positivity),eventually_ge_atTop (0:ℝ)] with H hH hpos
  have habs : f H ≤ |f H| := le_abs_self _
  simp only [Real.norm_eq_abs,abs_of_nonneg hpos] at hH
  dsimp only [id_eq]
  linarith

theorem fixed_linear_exp_isLittleO {a b : ℝ} (hab : a < b) :
    (fun H : ℝ => Real.exp (a*H)) =o[atTop] (fun H => Real.exp (b*H)) := by
  apply Real.isLittleO_exp_comp_exp_comp.mpr
  simpa only [sub_mul,id_eq] using tendsto_id.const_mul_atTop (sub_pos.mpr hab)

theorem derivative_split_exponent (k : ℕ) :
    let alpha : ℝ := 1/(4*((k:ℝ)+2))
    0 < alpha ∧ alpha < 1/(2*((k:ℝ)+2)) ∧
      ∀ j : ℕ, j ≤ k → alpha*((j:ℝ)+2) < 1/2 := by
  dsimp only
  have hk : 0 < (k:ℝ)+2 := by positivity
  refine ⟨by positivity,?_,?_⟩
  · apply one_div_lt_one_div_of_lt (by positivity)
    nlinarith
  · intro j hj
    have hjr : (j:ℝ) ≤ k := by exact_mod_cast hj
    rw [one_div_mul_eq_div]
    apply (div_lt_iff₀ (show 0 < 4*((k:ℝ)+2) by positivity)).mpr
    nlinarith

theorem gaussian_threshold_exists (k : ℕ) {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ D : ℝ, 0 < D ∧ (k:ℝ)+2 < kappa*D^2 := by
  refine ⟨Real.sqrt (((k:ℝ)+3)/kappa),Real.sqrt_pos.mpr (by positivity),?_⟩
  rw [Real.sq_sqrt (by positivity),mul_div_cancel₀ _ hkappa.ne']
  linarith

theorem shift_two_isBigO : (fun H : ℝ => H+2) =O[atTop] (fun H => H) := by
  apply Asymptotics.IsBigO.of_bound 3
  filter_upwards [eventually_ge_atTop (1:ℝ)] with H hH
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (by linarith),abs_of_nonneg (by linarith)]
  linarith

theorem log_square_shift_sublinear :
    (fun H : ℝ => Real.log (H+2)^2) =o[atTop] (fun H => H) := by
  have h : (fun H : ℝ => Real.log H^2) =o[atTop] (fun H => H) := by
    simpa only [Real.rpow_two,Real.rpow_one] using
      isLittleO_log_rpow_rpow_atTop (s := 1) 2 (by norm_num)
  have ht : Tendsto (fun H : ℝ => H+2) atTop atTop := tendsto_atTop_add_const_right atTop 2 tendsto_id
  exact (h.comp_tendsto ht).trans_isBigO shift_two_isBigO

theorem sqrt_log_shift_sublinear :
    (fun H : ℝ => Real.log (H+2)*Real.sqrt (H+2)) =o[atTop] (fun H => H) := by
  have hl : Real.log =o[atTop] Real.sqrt := by
    simpa only [← Real.sqrt_eq_rpow] using isLittleO_log_rpow_atTop (r := 1/2) (by norm_num)
  have hp := hl.mul_isBigO (Asymptotics.isBigO_refl Real.sqrt atTop)
  have h : (fun H : ℝ => Real.log H*Real.sqrt H) =o[atTop] (fun H => H) := by
    apply hp.congr' (Eventually.of_forall (fun _ => rfl))
    filter_upwards [eventually_ge_atTop (0:ℝ)] with H hH
    exact Real.mul_self_sqrt hH
  have ht : Tendsto (fun H : ℝ => H+2) atTop atTop := tendsto_atTop_add_const_right atTop 2 tendsto_id
  exact (h.comp_tendsto ht).trans_isBigO shift_two_isBigO

theorem selected_sum_growth_negligible (C : ℝ) :
    (fun H : ℝ => Real.exp (C*Real.log (H+2)^2)) =o[atTop]
      (fun H => Real.exp (H/2)) := by
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using
    exp_sublinear_isLittleO (log_square_shift_sublinear.const_mul_left C) (c := 1/2) (by norm_num)

theorem intermediate_sum_growth_negligible (C : ℝ) :
    (fun H : ℝ => Real.exp (C*(Real.log (H+2)*Real.sqrt (H+2)))) =o[atTop]
      (fun H => Real.exp (H/2)) := by
  simpa only [div_eq_mul_inv,mul_comm,one_mul] using
    exp_sublinear_isLittleO (sqrt_log_shift_sublinear.const_mul_left C) (c := 1/2) (by norm_num)

end
end IsingBulk.Tail
