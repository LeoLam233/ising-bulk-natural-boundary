import IsingBulk.Tail.SelectedFSeriesBound
import IsingBulk.Tail.SummationGrowth
import IsingBulk.Tail.UltraHighRadialTail

/-! Actual selected-F absolute derivative series is negligible at the FIRST
inverse-square-root scale. This uses its proved source estimate, not a new
sector-bound premise. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Filter Asymptotics
open scoped Topology

theorem exp_half_log_inverse {e : ℝ} (he : 0 < e) :
    Real.exp (Real.log (1/e)/2)=(Real.sqrt e)⁻¹ := by
  have hleft : (Real.exp (Real.log (1/e)/2))^2=e⁻¹ := by
    rw [pow_two,← Real.exp_add,show Real.log (1/e)/2+Real.log (1/e)/2=Real.log (1/e) by ring,
      Real.exp_log (by positivity),one_div]
  have hright : ((Real.sqrt e)⁻¹)^2=e⁻¹ := by rw [inv_pow,Real.sq_sqrt he.le]
  nlinarith [Real.exp_pos (Real.log (1/e)/2),inv_pos.mpr (Real.sqrt_pos.mpr he)]

theorem radial_log_square_growth_littleO (C : ℝ) :
    (fun e : ℝ => Real.exp (C*Real.log (2-Real.log e)^2)) =o[𝓝[>] 0]
      (fun e : ℝ => (Real.sqrt e)⁻¹) := by
  have hh := (selected_sum_growth_negligible C).comp_tendsto log_inverse_tendsto_atTop
  apply hh.congr'
  · apply Eventually.of_forall
    intro e
    simp only [Function.comp_def,one_div,Real.log_inv,sub_eq_add_neg,add_comm]
  · filter_upwards [self_mem_nhdsWithin] with e he
    exact exp_half_log_inverse he

theorem selected_actual_full_series_littleO (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ eta0 tau0 : ℝ, 0 < eta0 ∧ 0 < tau0 ∧
      ∀ eta alpha tau : ℝ, 0 < eta → eta < eta0 → 0 < alpha → alpha < Real.sin d.thetaB/4 →
        0 < tau → tau < tau0 → ∀ j : ℕ,
          (fun eps : ℝ => ∑' n : ℕ, ‖iteratedDeriv j
            (selectedIntegral (2*(n+1)) (constructedSelector d.thetaB eta alpha)
              (Real.exp (-d.c₀*eps)) tau) (radialParameter d.theta eps)‖) =o[𝓝[>] 0]
                (fun eps : ℝ => (Real.sqrt eps)⁻¹) := by
  obtain ⟨eta0,tau0,heta0,htau0,hF⟩ := selected_actual_full_series_reqF d hcsmall
  refine ⟨eta0,tau0,heta0,htau0,?_⟩
  intro eta alpha tau heta hetaSmall halpha halphaSmall htau htauSmall j
  obtain ⟨e,C,he,hC,hbound⟩ := hF eta alpha tau heta hetaSmall halpha halphaSmall htau htauSmall j
  have hb : (fun eps : ℝ => ∑' n : ℕ, ‖iteratedDeriv j
      (selectedIntegral (2*(n+1)) (constructedSelector d.thetaB eta alpha)
        (Real.exp (-d.c₀*eps)) tau) (radialParameter d.theta eps)‖) =O[𝓝[>] 0]
          (fun eps : ℝ => Real.exp (C*Real.log (2-Real.log eps)^2)) := by
    apply IsBigO.of_bound 1
    filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ eps : ℝ in 𝓝[>] 0, eps < e from
        mem_nhdsWithin_of_mem_nhds (eventually_lt_nhds he))] with eps heps hsmall
    have hn : 0 ≤ ∑' n : ℕ, ‖iteratedDeriv j
        (selectedIntegral (2*(n+1)) (constructedSelector d.thetaB eta alpha)
          (Real.exp (-d.c₀*eps)) tau) (radialParameter d.theta eps)‖ := tsum_nonneg (fun _ => norm_nonneg _)
    simpa only [Real.norm_eq_abs,abs_of_nonneg hn,abs_of_pos (Real.exp_pos _),one_mul] using
      (hbound eps heps hsmall).2
  exact hb.trans_isLittleO (radial_log_square_growth_littleO C)

end
end IsingBulk.Tail
