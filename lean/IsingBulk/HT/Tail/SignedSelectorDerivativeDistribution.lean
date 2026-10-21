import IsingBulk.HT.Contour.SignedOriginalHolomorphy
import IsingBulk.HT.Contour.SignedRetraction
import IsingBulk.HT.Tail.SignedCurrentIntervalDerivatives

/-! All source derivatives of the literal signed F+K+S identity, with radius
and the complete real homotopy interval fixed before differentiation. -/
namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff

 theorem signed_sourceIntegral_analytic_on_damping (σ : ℂ) (hσ : ‖σ‖ = 1)
    (N : ℕ) (hN : 0 < N) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) :
    AnalyticOnNhd ℂ (signedSourceIntegral σ N r) (dampingDomain r) := by
  have ha := signed_weighted_homotopy_slice_analytic σ hσ N hN f hf hr hr1 hτ
    (show (0:ℝ) ≤ 0 from le_rfl) (fun _ => (1:ℂ)) continuous_const
  have he : (fun s => ∫ θ in angleBox N, (1:ℂ)*signedPulledDensity σ f r τ 0 s θ) =
      signedSourceIntegral σ N r := by
    funext s
    simpa only [one_mul,signedHomotopyTotal] using
      signedHomotopyTotal_zero_eq_source σ N f r τ s
  rw [he] at ha
  exact ha

 theorem signed_selector_eventually_eq (σ : ℂ) (hσ : ‖σ‖ = 1)
    (N : ℕ) (hN : 0 < N) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) {s : ℂ}
    (hs : s ∈ dampingDomain r) :
    signedSourceIntegral σ N r =ᶠ[𝓝 s] (fun z => signedSelectedIntegral σ N f r τ z+
      signedOriginalLowerIntegral σ N f r τ z+signedCurrentIntegral σ N f r τ z) := by
  filter_upwards [(dampingDomain_isOpen r).mem_nhds hs] with z hz
  exact exact_signed_weighted_retraction σ hσ N hN f hf hr hr1 hτ z hz.2

 theorem signed_currentIntegral_analytic_on_damping (σ : ℂ) (hσ : ‖σ‖ = 1)
    (N : ℕ) (hN : 0 < N) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) :
    AnalyticOnNhd ℂ (signedCurrentIntegral σ N f r τ) (dampingDomain r) := by
  obtain ⟨hF,hK⟩ := signed_selected_and_lower_analytic σ hσ N hN f hf hr hr1 hτ
  have hsource := signed_sourceIntegral_analytic_on_damping σ hσ N hN f hf hr hr1 hτ
  intro s hs
  have ha := ((hsource s hs).sub (hF s hs)).sub (hK s hs)
  apply ha.congr
  filter_upwards [signed_selector_eventually_eq σ hσ N hN f hf hr hr1 hτ hs] with z hz
  simp only [Pi.sub_apply]
  linear_combination hz

 theorem signed_selector_iteratedDeriv_distributed (σ : ℂ) (hσ : ‖σ‖ = 1)
    (N : ℕ) (hN : 0 < N) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) {s : ℂ}
    (hs : s ∈ dampingDomain r) (j : ℕ) :
    iteratedDeriv j (signedSourceIntegral σ N r) s =
      iteratedDeriv j (signedSelectedIntegral σ N f r τ) s+
      iteratedDeriv j (signedOriginalLowerIntegral σ N f r τ) s+
      iteratedDeriv j (signedCurrentIntegral σ N f r τ) s := by
  obtain ⟨hF,hK⟩ := signed_selected_and_lower_analytic σ hσ N hN f hf hr hr1 hτ
  have hS := signed_currentIntegral_analytic_on_damping σ hσ N hN f hf hr hr1 hτ s hs
  rw [(signed_selector_eventually_eq σ hσ N hN f hf hr hr1 hτ hs).iteratedDeriv_eq j]
  change iteratedDeriv j ((signedSelectedIntegral σ N f r τ+signedOriginalLowerIntegral σ N f r τ)+
    signedCurrentIntegral σ N f r τ) s = _
  rw [iteratedDeriv_add ((hF s hs).add (hK s hs)).contDiffAt hS.contDiffAt,
    iteratedDeriv_add (hF s hs).contDiffAt (hK s hs).contDiffAt]

 theorem signed_selector_iteratedDeriv_full_current (σ : ℂ) (hσ : ‖σ‖ = 1)
    (N : ℕ) (hN : 0 < N) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) {s : ℂ}
    (hs : s ∈ dampingDomain r) (j : ℕ) :
    iteratedDeriv j (signedSourceIntegral σ N r) s =
      iteratedDeriv j (signedSelectedIntegral σ N f r τ) s+
      iteratedDeriv j (signedOriginalLowerIntegral σ N f r τ) s+
      ∫ lam : ℝ in 0..1, signedDifferentiatedCurrentSlice σ N f r τ lam j s := by
  rw [signed_selector_iteratedDeriv_distributed σ hσ N hN f hf hr hr1 hτ hs j,
    signed_currentIntegral_iteratedDeriv σ hσ N hN f hr hr1 hτ hf.p_smooth hf.m_smooth hf.a_smooth
      hf.p_nonneg hf.m_nonneg hf.m_le_one hf.p_zero hf.m_zero j hs]

end
end IsingBulk.HT.Tail
