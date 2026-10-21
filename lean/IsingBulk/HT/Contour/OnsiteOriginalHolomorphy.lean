import IsingBulk.HT.Contour.OnsiteContinuation
import IsingBulk.Tail.SelectorDerivativeDistribution

namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Tail Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff
set_option maxHeartbeats 800000

theorem onsite_weighted_homotopy_slice_analytic (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ lam : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam)
    (weight : (Fin N → ℝ) → ℂ) (hweight : Continuous weight) :
    AnalyticOnNhd ℂ (fun s => ∫ θ in angleBox N,weight θ*onsitePulledDensity f r τ lam s θ)
      (dampingDomain r) := by
  let U := dampingDomain r
  let psi := deformedPoint (N := N) f r τ lam
  let chi := fun θ : Fin N → ℝ => weight θ*(N.factorial:ℂ)⁻¹*
    (2*(Real.pi:ℂ)*Complex.I)^(-(N:ℤ))*(angularJacobian f τ lam θ).det
  let F := onsiteContinuedContourDensity N
  have hU : IsOpen U := dampingDomain_isOpen r
  have hpsi : Continuous psi := deformedPoint_continuous f r τ lam
    hf.p_smooth.continuous hf.m_smooth.continuous
  have hJ : Continuous (fun θ : Fin N → ℝ => angularJacobian f τ lam θ) :=
    (angularJacobian_joint_contDiff f τ hf.p_smooth hf.m_smooth).continuous.comp
      (continuous_const.prodMk continuous_id)
  have hchi : Continuous chi := by dsimp [chi]; fun_prop
  have hupper (s : ℂ) (hs : s ∈ U) (θ : Fin N → ℝ) (i : Fin N) :
      0 < (sourceW s (psi θ i)).im := by
    have hbase := sourceW_upper_of_margin hr hr1 hs.2 (deformedPoint_zero_norm f hr.le τ θ i)
    exact hbase.trans_le (deformed_sourceW_im_ge hN f hr hτ hlam θ s hf.p_nonneg
      hf.m_nonneg hf.p_zero hf.m_zero i)
  have hF (s : ℂ) (hs : s ∈ U) (θ : Fin N → ℝ) (_hθ : θ ∈ angleBox N) :
      AnalyticAt ℂ F (s,psi θ) := by
    exact onsite_continuedContourDensity_analyticAt hs.1 (deformedPoint_nonzero f hr.ne' τ lam θ)
      (fun i => Or.inl (Or.inl (hupper s hs θ i)))
  intro s hs
  have han := compact_analytic_shape_integral_analyticAt (μ := volume) isCompact_Icc hU F
    psi hpsi chi hchi hF hs
  apply han.congr
  filter_upwards [hU.mem_nhds hs] with z hz
  apply setIntegral_congr_fun measurableSet_Icc
  intro θ _
  dsimp only
  rw [← onsite_continuedPulledDensity_eq_original f r τ lam z θ (hupper z hz θ)]
  dsimp [chi,F,psi,onsiteContinuedContourDensity,onsiteContinuedPulledDensity]
  ring

theorem onsite_selected_and_lower_analytic (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) :
    AnalyticOnNhd ℂ (onsiteSelectedIntegral N f r τ) (dampingDomain r) ∧
      AnalyticOnNhd ℂ (onsiteOriginalLowerIntegral N f r τ) (dampingDomain r) := by
  have ha : Continuous (fun θ : Fin N → ℝ => angularSelector f θ) := by
    have hfa := hf.a_smooth.continuous
    unfold angularSelector selectorWeight
    fun_prop
  exact ⟨onsite_weighted_homotopy_slice_analytic N hN f hf hr hr1 hτ (by norm_num)
      _ (Complex.continuous_ofReal.comp (continuous_const.sub ha)),
    onsite_weighted_homotopy_slice_analytic N hN f hf hr hr1 hτ le_rfl
      _ (Complex.continuous_ofReal.comp ha)⟩

end
end IsingBulk.HT.Contour
