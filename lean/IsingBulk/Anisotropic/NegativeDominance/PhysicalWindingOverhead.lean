import IsingBulk.Anisotropic.NegativeDominance.HigherWindingOverhead
import IsingBulk.Anisotropic.NegativeDominance.PhysicalSequences

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Filter IsingBulk.Anisotropic.NegativeNormalForm
open scoped Topology

private theorem eventually_abs_le_limit_add_one {f : ℕ→ℝ} {a : ℝ}
    (h : Tendsto f atTop (𝓝 a)) : ∀ᶠ N : ℕ in atTop, |f N|≤|a|+1 := by
  filter_upwards [Metric.tendsto_nhds.mp h 1 zero_lt_one] with N hN
  rw [Real.dist_eq] at hN
  linarith [abs_sub_abs_le_abs_sub (f N) a]

/-- Uniform quadratic normalization loss derived from the actual analytic
scalar data, not posited separately for the sequence of models. -/
theorem physical_higherWindingOverhead_entropy (B rootB : ℂ→ℂ) (phi M c : ℝ)
    (hB : AnalyticAt ℂ B 0) (hB0 : B 0≠0)
    (hr : ContinuousAt rootB 0) (hr0 : rootB 0≠0) (hs : Real.sin phi≠0)
    (hM : 1≤M) (hc : 0<c) :
    ∃C : ℝ,0<C ∧ ∀ᶠ N : ℕ in atTop,
      higherWindingOverhead M c (B (tau N)) (rootB (tau N))
        (hessianFactor (B (tau N)) (Real.cos phi) (Real.sin phi) N) (Real.sin phi) N≤
          Real.exp (C*(N : ℝ)^2) := by
  have hbLog : Tendsto (fun N : ℕ=>Real.log ‖B (tau N)‖) atTop (𝓝 (Real.log ‖B 0‖)) :=
    (Real.continuousAt_log (norm_ne_zero_iff.mpr hB0)).tendsto.comp
      (hB.continuousAt.tendsto.comp tau_complex_tendsto_zero).norm
  have hrLog : Tendsto (fun N : ℕ=>Real.log ‖rootB (tau N)‖) atTop (𝓝 (Real.log ‖rootB 0‖)) :=
    (Real.continuousAt_log (norm_ne_zero_iff.mpr hr0)).tendsto.comp
      (hr.tendsto.comp tau_complex_tendsto_zero).norm
  have hHlim : Tendsto (fun N : ℕ=>hessianFactor (B (tau N)) (Real.cos phi) (Real.sin phi) N)
      atTop (𝓝 (1 : ℂ)) := by
    simpa only [Function.comp_def,centralHessian_at_winding,centralHessian_zero] using
      (centralHessian_analyticAt_zero B phi hB).continuousAt.tendsto.comp winding_angle_complex_tendsto_zero
  have hHLog : Tendsto (fun N : ℕ=>Real.log ‖hessianFactor (B (tau N))
      (Real.cos phi) (Real.sin phi) N‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def,norm_one,Real.log_one] using
      (Real.continuousAt_log (show ‖(1 : ℂ)‖≠0 by simp)).tendsto.comp hHlim.norm
  let L := 3+|Real.log ‖B 0‖|+|Real.log ‖rootB 0‖|+|Real.log M|+|Real.log c|+
    |Real.log (|Real.sin phi|)|+|Real.log (2*Real.pi)|+|Real.log 2|
  have hLs : 1≤L ∧ |Real.log ‖B 0‖|+1≤L ∧ |Real.log ‖rootB 0‖|+1≤L ∧
      Real.log M≤L ∧ |Real.log c|≤L ∧ |Real.log (|Real.sin phi|)|≤L ∧
      Real.log (2*Real.pi)≤L ∧ Real.log 2≤L := by
    dsimp [L]
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
      linarith only [abs_nonneg (Real.log ‖B 0‖),abs_nonneg (Real.log ‖rootB 0‖),
        abs_nonneg (Real.log M),abs_nonneg (Real.log c),abs_nonneg (Real.log (|Real.sin phi|)),
        abs_nonneg (Real.log (2*Real.pi)),abs_nonneg (Real.log 2),
        le_abs_self (Real.log M),le_abs_self (Real.log (2*Real.pi)),le_abs_self (Real.log 2)]
  refine ⟨20*(L+1),by linarith [hLs.1],?_⟩
  filter_upwards [eventually_abs_le_limit_add_one hbLog,eventually_abs_le_limit_add_one hrLog,
    eventually_abs_le_limit_add_one hHLog,tau_complex_tendsto_zero.eventually (hB.continuousAt.eventually_ne hB0),
    tau_complex_tendsto_zero.eventually (hr.eventually_ne hr0),hessianFactor_eventually_nonzero B phi hB,
    eventually_ge_atTop (2 : ℕ)] with N hb hr' hH hb0 hr0' hH0 hN
  apply higherWindingOverhead_entropy M c _ _ _ (Real.sin phi) L hN hM hc hb0 hr0' hH0 hs hLs.1
  · exact hLs.2.2.2.1
  · exact hLs.2.2.2.2.1
  · exact hb.trans hLs.2.1
  · exact hr'.trans hLs.2.2.1
  · have hH' : |Real.log ‖hessianFactor (B (tau N)) (Real.cos phi) (Real.sin phi) N‖|≤1 := by
      simpa only [abs_zero,zero_add] using hH
    exact (le_abs_self _).trans (hH'.trans hLs.1)
  · exact hLs.2.2.2.2.2.1
  · exact hLs.2.2.2.2.2.2.1
  · exact hLs.2.2.2.2.2.2.2

end
end IsingBulk.Anisotropic.NegativeDominance
