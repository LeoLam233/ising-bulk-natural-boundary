import IsingBulk.HT22.Tail.LocalizedRegularity
import IsingBulk.HT22.Tail.SignedStokes

namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

def localizedCurrent {N : ℕ} (σ : ℂ) (τ : ℝ) (η p m r : ℝ → ℝ)
    (W : (Fin N → ℝ) → ℂ) (j : ℕ) (s : ℂ) (θ : Fin N → ℝ) (i : Fin N) : ℂ :=
  angularField τ p m s θ i*localizedPhysicalDensity σ τ η p m r W j s θ

theorem localizedCurrent_upper_zero {N : ℕ} (σ : ℂ) (d : PreferredBranchData)
    (B : PreferredCoareaBump d) (τ : ℝ) (rcut : ℝ → ℝ) (W : (Fin N → ℝ) → ℂ)
    (j : ℕ) (s : ℂ) (θ : Fin N → ℝ) (a : Fin N) (ha : 1/2<B.p (θ a)) (i : Fin N) :
    localizedCurrent σ τ preferredPopulationCutoff B.p B.m rcut W j s θ i=0 := by
  simp only [localizedCurrent,localizedPhysicalDensity_zero_of_upper_particle σ d B τ rcut W j s θ a ha,mul_zero]

theorem localized_density_current_lift_contDiffAt {N : ℕ} (hN : 0<N) (σ : ℂ) (hσ : ‖σ‖≤1)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB τ : ℝ}
    (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (W : (Fin N → ℝ) → ℂ) (hW : ContDiff ℝ ∞ W)
    (hzero : ∀x∈preferredRightAngularBox d B.delta δB N, preferredAngularDiameter x=0 → W=ᶠ[𝓝 x] fun _ => 0)
    (s : ℂ) (j : ℕ)
    (hreg : ∀x∈preferredRightAngularBox d B.delta δB N,0<preferredAngularDiameter x → RegularPoint τ B.p B.m s x)
    (θ : Fin N → ℝ) :
    ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) => localizedPhysicalDensity σ τ preferredPopulationCutoff B.p B.m rcut W j
      z.1 (preferredLiftedAngles B.delta z.2)) (s,θ) ∧ ∀i,
    ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) => localizedCurrent σ τ preferredPopulationCutoff B.p B.m rcut W j
      z.1 (preferredLiftedAngles B.delta z.2) i) (s,θ) := by
  constructor
  · apply preferredLiftedFunction_contDiffAt d B
      (fun z => localizedPhysicalDensity σ τ preferredPopulationCutoff B.p B.m rcut W j z.1 z.2)
      (fun t x a ha => localizedPhysicalDensity_zero_of_upper_particle σ d B τ rcut W j t x a ha) s θ
    intro hθ
    exact (localized_density_current_period_mixed hN σ hσ d B rcut hcut W hW hzero s j hreg _
      (fun i => ⟨(preferredLiftedAngles_mem_oneSided B.delta θ i).1,hθ i⟩)).1.1
  · intro i
    apply preferredLiftedFunction_contDiffAt d B
      (fun z => localizedCurrent σ τ preferredPopulationCutoff B.p B.m rcut W j z.1 z.2 i)
      (fun t x a ha => localizedCurrent_upper_zero σ d B τ rcut W j t x a ha i) s θ
    intro hθ
    exact (localized_density_current_period_mixed hN σ hσ d B rcut hcut W hW hzero s j hreg _
      (fun a => ⟨(preferredLiftedAngles_mem_oneSided B.delta θ a).1,hθ a⟩)).2 i

theorem localizedCurrent_contDiffAt {N : ℕ} (hN : 0<N) (σ : ℂ) (hσ : ‖σ‖≤1)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB τ : ℝ}
    (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (W : (Fin N → ℝ) → ℂ) (hW : ContDiff ℝ ∞ W)
    (hzero : ∀x∈preferredRightAngularBox d B.delta δB N, preferredAngularDiameter x=0 → W=ᶠ[𝓝 x] fun _ => 0)
    (s : ℂ) (j : ℕ)
    (hreg : ∀x∈preferredRightAngularBox d B.delta δB N,0<preferredAngularDiameter x → RegularPoint τ B.p B.m s x)
    (θ : Fin N → ℝ) (hθ : ∀i,θ i∈Ioc (-Real.pi-B.delta) (Real.pi-B.delta)) (i : Fin N) :
    ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) => localizedCurrent σ τ preferredPopulationCutoff B.p B.m rcut W j z.1 z.2 i) (s,θ) := by
  apply preferredPeriodIntervalFunction_contDiffAt d B _
    (fun t x a ha => localizedCurrent_upper_zero σ d B τ rcut W j t x a ha i) s θ hθ
  intro hθhi
  exact (localized_density_current_period_mixed hN σ hσ d B rcut hcut W hW hzero s j hreg θ
    (fun a => ⟨(hθ a).1,hθhi a⟩)).2 i

theorem localizedDensity_parameter_differentiable {N : ℕ} (hN : 0<N) (σ : ℂ) (hσ : ‖σ‖≤1)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB τ : ℝ}
    (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (W : (Fin N → ℝ) → ℂ) (hW : ContDiff ℝ ∞ W)
    (hzero : ∀x∈preferredRightAngularBox d B.delta δB N, preferredAngularDiameter x=0 → W=ᶠ[𝓝 x] fun _ => 0)
    (s : ℂ) (j : ℕ)
    (hreg : ∀x∈preferredRightAngularBox d B.delta δB N,0<preferredAngularDiameter x → RegularPoint τ B.p B.m s x)
    (θ : Fin N → ℝ) (hθ : ∀i,θ i∈Ioc (-Real.pi-B.delta) (Real.pi-B.delta)) :
    DifferentiableAt ℂ (fun t => localizedPhysicalDensity σ τ preferredPopulationCutoff B.p B.m rcut W j t θ) s := by
  by_cases hb : θ∈preferredRightAngularBox d B.delta δB N
  · by_cases hd : 0<preferredAngularDiameter θ
    · obtain ⟨δ,Ω,hΩ,hz,hpt,hR⟩ := hreg θ hb hd
      exact (localizedPhysicalDensity_mixed hN σ hσ τ δ preferredPopulationCutoff B.p B.m rcut
        preferredPopulationCutoff_smooth B.smooth B.m_smooth hcut.2.2.1 W hW Ω hΩ hpt hR j (s,θ) hz).2
    · have he := localizedPhysicalDensity_zero_germ σ τ preferredPopulationCutoff B.p B.m rcut W θ
        (hzero θ hb (le_antisymm (le_of_not_gt hd) Metric.diam_nonneg)) j s
      exact (differentiableAt_const (0:ℂ)).congr_of_eventuallyEq
        (he.comp_tendsto ((continuous_id.prodMk continuous_const).tendsto s))
  · have he : (fun t => localizedPhysicalDensity σ τ preferredPopulationCutoff B.p B.m rcut W j t θ)=fun _ => 0 :=
      funext (fun t => localizedPhysicalDensity_right_support σ d B τ rcut W hcut j t θ hθ hb)
    rw [he]
    exact differentiableAt_const _

theorem localizedCurrent_tangent {N : ℕ} (σ : ℂ) (d : PreferredBranchData)
    (B : PreferredCoareaBump d) {δB τ : ℝ} (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (W : (Fin N → ℝ) → ℂ)
    (hzero : ∀x∈preferredRightAngularBox d B.delta δB N, preferredAngularDiameter x=0 → W=ᶠ[𝓝 x] fun _ => 0)
    (s : ℂ) (j : ℕ)
    (hreg : ∀x∈preferredRightAngularBox d B.delta δB N,0<preferredAngularDiameter x → RegularPoint τ B.p B.m s x)
    (θ : Fin N → ℝ) (hθ : ∀i,θ i∈Ioo (-Real.pi-B.delta) (Real.pi-B.delta)) :
    (∑i,localizedCurrent σ τ preferredPopulationCutoff B.p B.m rcut W j s θ i)=0 := by
  by_cases hb : θ∈preferredRightAngularBox d B.delta δB N
  · by_cases hd : 0<preferredAngularDiameter θ
    · simp only [localizedCurrent,←Finset.sum_mul,
        angularField_regularPoint_tangent τ B.p B.m s θ (hreg θ hb hd),zero_mul]
    · have he := (localizedPhysicalDensity_zero_germ σ τ preferredPopulationCutoff B.p B.m rcut W θ
        (hzero θ hb (le_antisymm (le_of_not_gt hd) Metric.diam_nonneg)) j s).self_of_nhds
      simp only [localizedCurrent,he,mul_zero,Finset.sum_const_zero]
  · have he := localizedPhysicalDensity_right_support σ d B τ rcut W hcut j s θ
      (fun i => ⟨(hθ i).1,(hθ i).2.le⟩) hb
    simp only [localizedCurrent,he,mul_zero,Finset.sum_const_zero]

end
end IsingBulk.HT22.Tail
