import IsingBulk.HT.Contour.SignedContinuation
import IsingBulk.Tail.SelectorDerivativeDistribution

/-! Actual signed selected and original complete integrals are holomorphic
on the damping domain. The angular weight and radius remain fixed. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Tail Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff
set_option maxHeartbeats 800000

theorem signed_weighted_homotopy_slice_analytic (σ : ℂ) (hσ : ‖σ‖ = 1) (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ lam : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam)
    (weight : (Fin N → ℝ) → ℂ) (hweight : Continuous weight) :
    AnalyticOnNhd ℂ (fun s => ∫ θ in angleBox N,weight θ*signedPulledDensity σ f r τ lam s θ)
      (dampingDomain r) := by
  let U := dampingDomain r
  let psi := deformedPoint (N := N) f r τ lam
  let chi := fun θ : Fin N → ℝ => weight θ*(N.factorial:ℂ)⁻¹*
    (2*(Real.pi:ℂ)*Complex.I)^(-(N:ℤ))*(angularJacobian f τ lam θ).det
  let F := signedContinuedContourDensity σ N
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
    have hY := signed_gap_ne_zero σ _ hσ
      (homotopy_y_product_lt_one hN f hr hr1 hτ hlam θ hf.p_nonneg hf.m_le_one)
    have hZ : 1-σ*coordinateProduct (fun i => selectedContinuedRoot s (psi θ i)) ≠ 0 := by
      apply signed_product_gap_ne_zero hN σ hσ
      intro i
      unfold selectedContinuedRoot
      rw [continuedRoot_eq_interiorRoot (hupper s hs θ i)]
      exact interiorRoot_norm_lt_one (hupper s hs θ i)
    exact signed_continuedContourDensity_analyticAt σ hs.1 (deformedPoint_nonzero f hr.ne' τ lam θ)
      (fun i => Or.inl (Or.inl (hupper s hs θ i))) hY hZ
  intro s hs
  have han := compact_analytic_shape_integral_analyticAt (μ := volume) isCompact_Icc hU F
    psi hpsi chi hchi hF hs
  apply han.congr
  filter_upwards [hU.mem_nhds hs] with z hz
  apply setIntegral_congr_fun measurableSet_Icc
  intro θ _
  dsimp only
  rw [← signed_continuedPulledDensity_eq_original σ f r τ lam z θ (hupper z hz θ)]
  dsimp [chi,F,psi,signedContinuedContourDensity,signedContinuedPulledDensity]
  ring

theorem signed_selected_and_lower_analytic (σ : ℂ) (hσ : ‖σ‖ = 1) (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) :
    AnalyticOnNhd ℂ (signedSelectedIntegral σ N f r τ) (dampingDomain r) ∧
      AnalyticOnNhd ℂ (signedOriginalLowerIntegral σ N f r τ) (dampingDomain r) := by
  have ha : Continuous (fun θ : Fin N → ℝ => angularSelector f θ) := by
    have hfa := hf.a_smooth.continuous
    unfold angularSelector selectorWeight
    fun_prop
  exact ⟨signed_weighted_homotopy_slice_analytic σ hσ N hN f hf hr hr1 hτ (by norm_num)
      _ (Complex.continuous_ofReal.comp (continuous_const.sub ha)),
    signed_weighted_homotopy_slice_analytic σ hσ N hN f hf hr hr1 hτ le_rfl
      _ (Complex.continuous_ofReal.comp ha)⟩

end
end IsingBulk.HT.Contour
