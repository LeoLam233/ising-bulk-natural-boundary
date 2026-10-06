import IsingBulk.Tail.SelectorRadialTheorem
import IsingBulk.Tail.CurrentIntervalDerivatives
import IsingBulk.First.FormFactorAnalytic

/-! Derivatives of the exact F+K+S identity are distributed only after proving
local analyticity of the actual complete integrals with radius fixed. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff
set_option maxHeartbeats 800000

theorem weighted_homotopy_slice_analytic (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ lam : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam)
    (weight : (Fin N → ℝ) → ℂ) (hweight : Continuous weight) :
    AnalyticOnNhd ℂ (fun s => ∫ θ in angleBox N,weight θ*pulledDensity f r τ lam s θ)
      (dampingDomain r) := by
  let U := dampingDomain r
  let psi := deformedPoint (N := N) f r τ lam
  let chi := fun θ : Fin N → ℝ => weight θ*(N.factorial:ℂ)⁻¹*
    (2*(Real.pi:ℂ)*Complex.I)^(-(N:ℤ))*(angularJacobian f τ lam θ).det
  let F := continuedContourDensity N
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
    have hY := homotopy_y_gap_nonzero hN f hr hr1 hτ hlam θ hf.p_nonneg hf.m_le_one
    have hZ : 1-coordinateProduct (fun i => selectedContinuedRoot s (psi θ i)) ≠ 0 := by
      apply one_sub_coordinateProduct_ne_zero hN
      intro i
      unfold selectedContinuedRoot
      rw [continuedRoot_eq_interiorRoot (hupper s hs θ i)]
      exact interiorRoot_norm_lt_one (hupper s hs θ i)
    exact continuedContourDensity_analyticAt hs.1 (deformedPoint_nonzero f hr.ne' τ lam θ)
      (fun i => Or.inl (Or.inl (hupper s hs θ i))) hY hZ
  intro s hs
  have han := compact_analytic_shape_integral_analyticAt (μ := volume) isCompact_Icc hU F
    psi hpsi chi hchi hF hs
  apply han.congr
  filter_upwards [hU.mem_nhds hs] with z hz
  apply setIntegral_congr_fun measurableSet_Icc
  intro θ _
  dsimp only
  rw [← continuedPulledDensity_eq_original f r τ lam z θ (hupper z hz θ)]
  dsimp [chi,F,psi,continuedContourDensity,continuedPulledDensity]
  ring

theorem selected_and_lower_analytic (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) :
    AnalyticOnNhd ℂ (selectedIntegral N f r τ) (dampingDomain r) ∧
      AnalyticOnNhd ℂ (originalLowerIntegral N f r τ) (dampingDomain r) := by
  have ha : Continuous (fun θ : Fin N → ℝ => angularSelector f θ) := by
    have hfa := hf.a_smooth.continuous
    unfold angularSelector selectorWeight
    fun_prop
  exact ⟨weighted_homotopy_slice_analytic N hN f hf hr hr1 hτ (by norm_num)
      _ (Complex.continuous_ofReal.comp (continuous_const.sub ha)),
    weighted_homotopy_slice_analytic N hN f hf hr hr1 hτ le_rfl
      _ (Complex.continuous_ofReal.comp ha)⟩

theorem currentIntegral_analytic_on_damping (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) :
    AnalyticOnNhd ℂ (currentIntegral N f r τ) (dampingDomain r) := by
  obtain ⟨hF,hK⟩ := selected_and_lower_analytic N hN f hf hr hr1 hτ
  intro s hs
  have hinv : 1 < r⁻¹ := (one_lt_inv₀ hr).mpr hr1
  have hupper : 0 < (sourceS s).im := by linarith [hs.2]
  have ha := ((upperFormFactor_analyticAt N hN hupper).sub (hF s hs)).sub (hK s hs)
  apply ha.congr
  filter_upwards [selector_eventually_eq N hN f hf hr hr1 hτ hs.2] with z hz
  simp only [Pi.sub_apply]
  linear_combination hz

theorem selector_iteratedDeriv_distributed (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) {s : ℂ}
    (hs : s ∈ dampingDomain r) (j : ℕ) :
    iteratedDeriv j (upperFormFactor N) s =
      iteratedDeriv j (selectedIntegral N f r τ) s+
      iteratedDeriv j (originalLowerIntegral N f r τ) s+
      iteratedDeriv j (currentIntegral N f r τ) s := by
  obtain ⟨hF,hK⟩ := selected_and_lower_analytic N hN f hf hr hr1 hτ
  have hS := currentIntegral_analytic_on_damping N hN f hf hr hr1 hτ s hs
  rw [selector_iteratedDeriv_eq N hN f hf hr hr1 hτ hs.2 j]
  change iteratedDeriv j ((selectedIntegral N f r τ+originalLowerIntegral N f r τ)+
    currentIntegral N f r τ) s = _
  rw [iteratedDeriv_add ((hF s hs).add (hK s hs)).contDiffAt hS.contDiffAt,
    iteratedDeriv_add (hF s hs).contDiffAt (hK s hs).contDiffAt]

theorem selector_iteratedDeriv_full_current (N : ℕ) (hN : 0 < N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) {s : ℂ}
    (hs : s ∈ dampingDomain r) (j : ℕ) :
    iteratedDeriv j (upperFormFactor N) s =
      iteratedDeriv j (selectedIntegral N f r τ) s+
      iteratedDeriv j (originalLowerIntegral N f r τ) s+
      ∫ lam : ℝ in 0..1,differentiatedCurrentSlice N f r τ lam j s := by
  rw [selector_iteratedDeriv_distributed N hN f hf hr hr1 hτ hs j,
    currentIntegral_iteratedDeriv N hN f hr hr1 hτ hf.p_smooth hf.m_smooth hf.a_smooth
      hf.p_nonneg hf.m_nonneg hf.m_le_one hf.p_zero hf.m_zero j hs]

end
end IsingBulk.Tail
