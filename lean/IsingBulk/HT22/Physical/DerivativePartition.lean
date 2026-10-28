import IsingBulk.HT22.Physical.WeightedAnalytic
namespace IsingBulk.HT22.Physical
noncomputable section
open Set Filter IsingBulk.Preferred22
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false

theorem complete_cell_partition (negative : Bool) (n : ℕ)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {τ : ℝ} (hτ : 0≤τ)
    (r : ℝ → ℝ) (hr : Continuous r) {t : ℂ} (ht : 1<‖t‖) (hS : 0<(temperatureTrace t).im) :
    signedCoefficient negative (n+1) t=
      fullPopulationIntegral negative n τ preferredPopulationCutoff B.p B.m t+
        2*(rightPopulationIntegral negative n τ preferredPopulationCutoff B.p B.m r t+
          ∑ a : Fin (n+1),anchorPopulationIntegral negative n a τ preferredPopulationCutoff B.p B.m r t) := by
  have hc : Continuous (bareContourDensity negative τ B.p B.m t (N:=n+1)) := by
    apply bareContourDensity_continuous negative (by omega) τ B.p B.m B.smooth B.m_smooth t
      (norm_ne_zero_iff.mp (by linarith))
    intro θ i
    have hW := homotopy_complexW_im_pos hS hτ (by norm_num : (0:ℝ)≤1) B.p B.m θ
      B.lower_bound (fun x => B.lower_bound (-x))
      (fun _ hx => B.p_zero_of_sin_nonpos hx) (fun _ hx => B.m_zero_of_sin_nonneg hx) i
    rw [complexW_homotopyRoot_eq] at hW
    exact Or.inl hW.ne'
  have hp := complete_population_partition negative n ht hS τ hτ B.p B.smooth B.periodic
    B.lower_bound (fun _ hx => B.p_zero_of_sin_nonpos hx) preferredPopulationCutoff preferredPopulationCutoff_smooth.continuous
  change signedCoefficient negative (n+1) t=fullPopulationIntegral negative n τ preferredPopulationCutoff B.p B.m t+
    2*lowerPopulationIntegral negative n τ preferredPopulationCutoff B.p B.m t at hp
  rw [lower_population_eq_right_add_anchors negative n τ preferredPopulationCutoff B.p B.m r t hc
    preferredPopulationCutoff_smooth.continuous B.smooth.continuous B.m_smooth.continuous hr] at hp
  exact hp

/-- Exact all-order signed coefficient decomposition on a common open upper
trace/exterior neighborhood. No derivative exchange or sum identity is assumed. -/
theorem complete_derivative_partition (negative : Bool) (n : ℕ)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {τ : ℝ} (hτ : 0≤τ)
    (r : ℝ → ℝ) (hr : ContDiff ℝ ∞ r) (j : ℕ) {s : ℂ}
    (hs : 1<‖s‖) (hS : 0<(temperatureTrace s).im) :
    iteratedDeriv j (signedCoefficient negative (n+1)) s=
      iteratedDeriv j (fullPopulationIntegral negative n τ preferredPopulationCutoff B.p B.m) s+
        2*(iteratedDeriv j (rightPopulationIntegral negative n τ preferredPopulationCutoff B.p B.m r) s+
          ∑ a : Fin (n+1),iteratedDeriv j
            (anchorPopulationIntegral negative n a τ preferredPopulationCutoff B.p B.m r) s) := by
  let F := fullPopulationIntegral negative n τ preferredPopulationCutoff B.p B.m
  let R := rightPopulationIntegral negative n τ preferredPopulationCutoff B.p B.m r
  let A := fun a : Fin (n+1) => anchorPopulationIntegral negative n a τ preferredPopulationCutoff B.p B.m r
  have hF : AnalyticAt ℂ F s := fullPopulationIntegral_analyticAt negative n d B hτ _
    preferredPopulationCutoff_smooth.continuous hS
  have hR : AnalyticAt ℂ R s := rightPopulationIntegral_analyticAt negative n d B hτ _ r
    preferredPopulationCutoff_smooth hr hS
  have hA (a : Fin (n+1)) : AnalyticAt ℂ (A a) s := anchorPopulationIntegral_analyticAt negative n a d B hτ _ r
    preferredPopulationCutoff_smooth hr hS
  have hAs : AnalyticAt ℂ (fun t => ∑ a,A a t) s := Finset.univ.analyticAt_fun_sum (fun a _ => hA a)
  obtain ⟨δ,hδ,hU⟩ := preferred_trace_upper_neighborhood hS
  have he : signedCoefficient negative (n+1) =ᶠ[𝓝 s] (fun t => F t+2*(R t+∑ a,A a t)) := by
    filter_upwards [Metric.ball_mem_nhds s hδ,continuous_norm.continuousAt.eventually (eventually_gt_nhds hs)] with t ht htn
    exact complete_cell_partition negative n d B hτ r hr.continuous htn (hU t ht).2
  rw [he.iteratedDeriv_eq]
  have hsecond : AnalyticAt ℂ (fun t => (2:ℂ)*(R t+∑ a,A a t)) s :=
    analyticAt_const.mul (hR.add hAs)
  rw [iteratedDeriv_fun_add hF.contDiffAt hsecond.contDiffAt,iteratedDeriv_const_mul_field,
    iteratedDeriv_fun_add hR.contDiffAt hAs.contDiffAt,iteratedDeriv_fun_sum (fun a _ => (hA a).contDiffAt)]
end
end IsingBulk.HT22.Physical
