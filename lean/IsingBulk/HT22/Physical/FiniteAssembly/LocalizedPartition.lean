import IsingBulk.HT22.Physical.FiniteAssembly.LocalizedRight
namespace IsingBulk.HT22.Physical.FiniteAssembly
noncomputable section
open Set Filter MeasureTheory IsingBulk.Preferred22
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

def rightFreeDensity (negative : Bool) (n : ℕ) (τ : ℝ) (p m r : ℝ → ℝ)
    (t : ℂ) (θ : Fin n → ℝ) : ℂ :=
  (preferredCellWeight .right preferredPopulationCutoff p m r (constrainedAngles negative n θ):ℂ)*
    bareContourDensity negative τ p m t (constrainedAngles negative n θ)

theorem rightFreeDensity_continuous (negative : Bool) (n : ℕ)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {τ : ℝ} (hτ : 0≤τ)
    (r : ℝ → ℝ) (hr : ContDiff ℝ ∞ r) {t : ℂ} (hS : 0<(temperatureTrace t).im) :
    Continuous (rightFreeDensity negative n τ B.p B.m r t) := by
  have ht : t≠0 := by intro hh;subst t;simp [temperatureTrace] at hS
  have hb := bareContourDensity_continuous negative (by omega : 0<n+1) τ B.p B.m B.smooth B.m_smooth t ht
    (fun θ i => by
      have hh := homotopy_complexW_im_pos hS hτ (by norm_num : (0:ℝ)≤1) B.p B.m θ
        B.lower_bound (fun x => B.lower_bound (-x))
        (fun _ hx => B.p_zero_of_sin_nonpos hx) (fun _ hx => B.m_zero_of_sin_nonneg hx) i
      rw [complexW_homotopyRoot_eq] at hh
      exact Or.inl hh.ne')
  exact ((Complex.continuous_ofReal.comp (preferredCellWeight_contDiff .right preferredPopulationCutoff B.p B.m r
    preferredPopulationCutoff_smooth B.smooth B.m_smooth hr).continuous).mul hb).comp
      (constrainedAngles_continuous negative n)

theorem localizedRight_integrable (negative : Bool) (n : ℕ)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {τ : ℝ} (hτ : 0≤τ)
    (r : ℝ → ℝ) (hr : ContDiff ℝ ∞ r) (χ : (Fin n → ℝ) → ℝ) (hχ : Continuous χ)
    {t : ℂ} (hS : 0<(temperatureTrace t).im) :
    IntegrableOn (fun θ => (χ θ:ℂ)*rightFreeDensity negative n τ B.p B.m r t θ) (angularBox n) := by
  have hc := (Complex.continuous_ofReal.comp hχ).mul (rightFreeDensity_continuous negative n d B hτ r hr hS)
  apply (hc.continuousOn.integrableOn_compact (isCompact_univ_pi (fun _ => isCompact_Icc))).mono_set
  intro θ hθ i _
  exact ⟨(hθ i (by simp)).1.le,(hθ i (by simp)).2⟩

theorem localizedRightIntegral_eq_weighted (negative : Bool) (n : ℕ)
    (τ : ℝ) (p m r : ℝ → ℝ) (χ : (Fin n → ℝ) → ℝ) :
    localizedRightIntegral negative n τ p m r χ=
      weightedIntegral (volume.restrict (angularBox n)) (rightFreeDensity negative n τ p m r) χ := by
  funext t
  simp only [localizedRightIntegral,weightedIntegral,rightFreeDensity,mul_assoc]

theorem actual_right_local_partition (negative : Bool) (n : ℕ)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {τ : ℝ} (hτ : 0≤τ)
    (r : ℝ → ℝ) (hr : ContDiff ℝ ∞ r) (P : List ((Fin n → ℝ) → ℝ))
    (rem : (Fin n → ℝ) → ℝ) (hP : ∀ ψ∈P,Continuous ψ) (hrem : Continuous rem)
    (hpartition : ∀ θ,(P.map (fun ψ => ψ θ)).sum+rem θ=1)
    {t : ℂ} (hS : 0<(temperatureTrace t).im) :
    rightPopulationIntegral negative n τ preferredPopulationCutoff B.p B.m r t=
      (P.map (fun ψ => localizedRightIntegral negative n τ B.p B.m r ψ t)).sum+
        localizedRightIntegral negative n τ B.p B.m r rem t := by
  have hh := weighted_integral_partition (volume.restrict (angularBox n))
    (rightFreeDensity negative n τ B.p B.m r) P rem hpartition t
    (fun ψ hψ => localizedRight_integrable negative n d B hτ r hr ψ (hP ψ hψ) hS)
    (localizedRight_integrable negative n d B hτ r hr rem hrem hS)
  simpa only [←localizedRightIntegral_eq_weighted,rightFreeDensity,rightPopulationIntegral,weightedContourIntegral] using hh

theorem actual_right_local_derivative_partition (negative : Bool) (n : ℕ)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {τ : ℝ} (hτ : 0≤τ)
    (r : ℝ → ℝ) (hr : ContDiff ℝ ∞ r) (P : List ((Fin n → ℝ) → ℝ))
    (rem : (Fin n → ℝ) → ℝ) (hP : ∀ ψ∈P,Continuous ψ) (hrem : Continuous rem)
    (hpartition : ∀ θ,(P.map (fun ψ => ψ θ)).sum+rem θ=1)
    {s : ℂ} (hS : 0<(temperatureTrace s).im) (j : ℕ) :
    iteratedDeriv j (rightPopulationIntegral negative n τ preferredPopulationCutoff B.p B.m r) s=
      (P.map (fun ψ => iteratedDeriv j (localizedRightIntegral negative n τ B.p B.m r ψ) s)).sum+
        iteratedDeriv j (localizedRightIntegral negative n τ B.p B.m r rem) s := by
  obtain ⟨δ,hδ,hU⟩ := preferred_trace_upper_neighborhood hS
  have he : rightPopulationIntegral negative n τ preferredPopulationCutoff B.p B.m r =ᶠ[𝓝 s]
      (fun t => (P.map (fun ψ => localizedRightIntegral negative n τ B.p B.m r ψ t)).sum+
        localizedRightIntegral negative n τ B.p B.m r rem t) := by
    filter_upwards [Metric.ball_mem_nhds s hδ] with t ht
    exact actual_right_local_partition negative n d B hτ r hr P rem hP hrem hpartition (hU t ht).2
  have hh := iteratedDeriv_partition _ _ (P.map (localizedRightIntegral negative n τ B.p B.m r)) s
    (by simpa only [List.map_map,Function.comp_def] using he)
    (by intro f hf; obtain ⟨ψ,hψ,rfl⟩ := List.mem_map.mp hf
        exact localizedRightIntegral_analyticAt negative n d B hτ r hr ψ (hP ψ hψ) hS)
    (localizedRightIntegral_analyticAt negative n d B hτ r hr rem hrem hS) j
  simpa only [List.map_map,Function.comp_def] using hh
end
end IsingBulk.HT22.Physical.FiniteAssembly
