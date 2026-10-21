import IsingBulk.HT.Contour.OnsiteOriginalHolomorphy
import IsingBulk.HT.Contour.OnsiteSourceBridge

/-! Exact onsite F+K+S derivative distribution with radius fixed, followed
by the actual canonical onsite derivative attachment. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Final Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff

 theorem onsite_sourceIntegral_analytic_on_damping (N : ℕ) (hN : 0 < N) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) :
    AnalyticOnNhd ℂ (onsiteSourceIntegral N r) (dampingDomain r) := by
  have ha := onsite_weighted_homotopy_slice_analytic N hN f hf hr hr1 hτ
    (show (0:ℝ) ≤ 0 from le_rfl) (fun _ => (1:ℂ)) continuous_const
  have he : (fun s => ∫ θ in angleBox N, (1:ℂ)*onsitePulledDensity f r τ 0 s θ) =
      onsiteSourceIntegral N r := by
    funext s
    simpa only [one_mul,onsiteHomotopyTotal] using
      onsiteHomotopyTotal_zero_eq_source N f r τ s
  rw [he] at ha
  exact ha

 theorem onsite_selector_eventually_eq (N : ℕ) (hN : 0 < N) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) {s : ℂ}
    (hs : s ∈ dampingDomain r) :
    onsiteSourceIntegral N r =ᶠ[𝓝 s] (fun z => onsiteSelectedIntegral N f r τ z+
      onsiteOriginalLowerIntegral N f r τ z+onsiteCurrentIntegral N f r τ z) := by
  filter_upwards [(dampingDomain_isOpen r).mem_nhds hs] with z hz
  exact exact_onsite_weighted_retraction N hN f hf hr hr1 hτ z hz.2

 theorem onsite_currentIntegral_analytic_on_damping (N : ℕ) (hN : 0 < N) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) :
    AnalyticOnNhd ℂ (onsiteCurrentIntegral N f r τ) (dampingDomain r) := by
  obtain ⟨hF,hK⟩ := onsite_selected_and_lower_analytic N hN f hf hr hr1 hτ
  have hsource := onsite_sourceIntegral_analytic_on_damping N hN f hf hr hr1 hτ
  intro s hs
  have ha := ((hsource s hs).sub (hF s hs)).sub (hK s hs)
  apply ha.congr
  filter_upwards [onsite_selector_eventually_eq N hN f hf hr hr1 hτ hs] with z hz
  simp only [Pi.sub_apply]
  linear_combination hz

 theorem onsite_selector_iteratedDeriv_distributed (N : ℕ) (hN : 0 < N) (f : SelectorFunctions) (hf : RegularSelector f)
    {r τ : ℝ} (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) {s : ℂ}
    (hs : s ∈ dampingDomain r) (j : ℕ) :
    iteratedDeriv j (onsiteSourceIntegral N r) s =
      iteratedDeriv j (onsiteSelectedIntegral N f r τ) s+
      iteratedDeriv j (onsiteOriginalLowerIntegral N f r τ) s+
      iteratedDeriv j (onsiteCurrentIntegral N f r τ) s := by
  obtain ⟨hF,hK⟩ := onsite_selected_and_lower_analytic N hN f hf hr hr1 hτ
  have hS := onsite_currentIntegral_analytic_on_damping N hN f hf hr hr1 hτ s hs
  rw [(onsite_selector_eventually_eq N hN f hf hr hr1 hτ hs).iteratedDeriv_eq j]
  change iteratedDeriv j ((onsiteSelectedIntegral N f r τ+onsiteOriginalLowerIntegral N f r τ)+
    onsiteCurrentIntegral N f r τ) s = _
  rw [iteratedDeriv_add ((hF s hs).add (hK s hs)).contDiffAt hS.contDiffAt,
    iteratedDeriv_add (hF s hs).contDiffAt (hK s hs).contDiffAt]

theorem upperOnsiteFormFactor_selector_iteratedDeriv (N : ℕ) (hN : 0<N)
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ : ℝ}
    (hr : 0<r) (hr1 : r<1) (hτ : 0≤τ) {s : ℂ} (hs : s∈dampingDomain r) (j : ℕ) :
    iteratedDeriv j (upperOnsiteFormFactor N) s=
      iteratedDeriv j (onsiteSelectedIntegral N f r τ) s+
      iteratedDeriv j (onsiteOriginalLowerIntegral N f r τ) s+
      iteratedDeriv j (onsiteCurrentIntegral N f r τ) s := by
  rw [upperOnsiteFormFactor_iteratedDeriv_eq_source N hN j hr hr1 hs.2]
  exact onsite_selector_iteratedDeriv_distributed N hN f hf hr hr1 hτ hs j

end
end IsingBulk.HT.Contour
