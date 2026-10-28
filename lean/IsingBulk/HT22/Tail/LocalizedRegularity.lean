import IsingBulk.HT22.Tail.LocalizedSupport
import IsingBulk.HT22.Tail.RegularPoint
import IsingBulk.HT22.Tail.PuncturedGeometry

namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 Set Filter
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false

theorem localizedPhysicalDensity_mixed {N : ℕ} (hN : 0<N) (σ : ℂ) (hσ : ‖σ‖≤1)
    (τ δ : ℝ) (η p m r : ℝ → ℝ)
    (hη : ContDiff ℝ ∞ η) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (hr : ContDiff ℝ ∞ r)
    (W : (Fin N → ℝ) → ℂ) (hW : ContDiff ℝ ∞ W)
    (Ω : Set (ℂ × (Fin N → ℝ))) (hΩ : IsOpen Ω)
    (hpoint : ∀ z∈Ω, PreferredFramePoint τ δ p m z.1 z.2)
    (hR : ∀ z∈Ω, sourceCovariance z.1 (sourceCoordinate τ p m z.1 z.2)≠0) (j : ℕ) :
    PreferredMixedSmoothOn (fun z => localizedPhysicalDensity σ τ η p m r W j z.1 z.2) Ω := by
  have hJ := coordinateJacobian_mixed τ δ p m hp hm Ω hpoint
  have hH := sourceSignedResolvent_mixed hN σ hσ τ δ p m hp hm Ω hpoint
  have hA := localizedSeed_mixed τ δ η p m r hη hp hm hr W hW Ω hΩ hpoint hR
  have hG := scalarIterate_mixed τ δ p m hp hm Ω hΩ hpoint hR _ hA j
  apply ((hJ.mul hH).mul hG).congr hΩ
  intro z hz
  exact (localizedPhysicalDensity_factorization hN σ hσ τ δ η p m r hη hp hm hr W hW
    Ω hΩ hpoint hR j z.1 z.2 hz).symm

theorem localizedPhysicalDensity_zero_germ {N : ℕ} (σ : ℂ) (τ : ℝ) (η p m r : ℝ → ℝ)
    (W : (Fin N → ℝ) → ℂ) (θ : Fin N → ℝ) (hW : W=ᶠ[𝓝 θ] fun _ => 0)
    (j : ℕ) (s : ℂ) :
    (fun z : ℂ × (Fin N → ℝ) => localizedPhysicalDensity σ τ η p m r W j z.1 z.2)
      =ᶠ[𝓝 (s,θ)] fun _ => 0 := by
  obtain ⟨U,hU,hUo,hθ⟩ := mem_nhds_iff.mp hW
  have hz : ∀t x,x∈U → localizedPhysicalDensity σ τ η p m r W j t x=0 :=
    localizedPhysicalDensity_zero_on_open σ τ η p m r W U hUo
      (fun t x hx => by rw [show W x=0 from hU hx,zero_mul]) j
  filter_upwards [continuousAt_snd.tendsto.eventually (hUo.mem_nhds hθ)] with z hz'
  exact hz z.1 z.2 hz'

/-- The localized original density is smooth on the whole one-sided period.
Only a genuine zero germ of the real weight is needed at full equality. -/
theorem localized_density_current_period_mixed {N : ℕ} (hN : 0<N) (σ : ℂ) (hσ : ‖σ‖≤1)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {δB τ : ℝ}
    (rcut : ℝ → ℝ) (hcut : PreferredRightCutoffData d B δB rcut)
    (W : (Fin N → ℝ) → ℂ) (hW : ContDiff ℝ ∞ W)
    (hzero : ∀x∈preferredRightAngularBox d B.delta δB N, preferredAngularDiameter x=0 → W=ᶠ[𝓝 x] fun _ => 0)
    (s : ℂ) (j : ℕ)
    (hreg : ∀x∈preferredRightAngularBox d B.delta δB N,0<preferredAngularDiameter x →
      RegularPoint τ B.p B.m s x)
    (θ : Fin N → ℝ) (hθ : ∀i,θ i∈Ioo (-Real.pi-B.delta) (Real.pi-B.delta)) :
    (ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) =>
      localizedPhysicalDensity σ τ preferredPopulationCutoff B.p B.m rcut W j z.1 z.2) (s,θ) ∧
      DifferentiableAt ℂ (fun t => localizedPhysicalDensity σ τ preferredPopulationCutoff B.p B.m rcut W j t θ) s) ∧
    ∀i,ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) => angularField τ B.p B.m z.1 z.2 i*
      localizedPhysicalDensity σ τ preferredPopulationCutoff B.p B.m rcut W j z.1 z.2) (s,θ) := by
  let P := localizedPhysicalDensity σ τ preferredPopulationCutoff B.p B.m rcut W j
  have fromzero (he : (fun z : ℂ × (Fin N → ℝ) => P z.1 z.2)=ᶠ[𝓝 (s,θ)] fun _ => 0) :
      (ContDiffAt ℝ ∞ (fun z : ℂ × (Fin N → ℝ) => P z.1 z.2) (s,θ) ∧
      DifferentiableAt ℂ (fun t => P t θ) s) ∧ ∀i,ContDiffAt ℝ ∞
        (fun z : ℂ × (Fin N → ℝ) => angularField τ B.p B.m z.1 z.2 i*P z.1 z.2) (s,θ) := by
    refine ⟨⟨contDiffAt_const.congr_of_eventuallyEq he,?_⟩,?_⟩
    · have hh := he.comp_tendsto ((continuous_id.prodMk continuous_const).tendsto s)
      exact (differentiableAt_const (0:ℂ)).congr_of_eventuallyEq hh
    · intro i
      apply contDiffAt_const.congr_of_eventuallyEq
      filter_upwards [he] with z hz
      rw [hz,mul_zero]
  by_cases hb : θ∈preferredRightAngularBox d B.delta δB N
  · by_cases hd : 0<preferredAngularDiameter θ
    · obtain ⟨δ,Ω,hΩ,hz,hpt,hR⟩ := hreg θ hb hd
      have hm := localizedPhysicalDensity_mixed hN σ hσ τ δ preferredPopulationCutoff B.p B.m rcut
        preferredPopulationCutoff_smooth B.smooth B.m_smooth hcut.2.2.1 W hW Ω hΩ hpt hR j (s,θ) hz
      exact ⟨hm,fun i => (angularField_regularPoint τ B.p B.m B.smooth B.m_smooth s θ
        (hreg θ hb hd) i).mul hm.1⟩
    · exact fromzero (localizedPhysicalDensity_zero_germ σ τ preferredPopulationCutoff B.p B.m rcut W θ
        (hzero θ hb (le_antisymm (le_of_not_gt hd) Metric.diam_nonneg)) j s)
  · have hc : IsClosed (preferredRightAngularBox d B.delta δB N) := by
      have he : preferredRightAngularBox d B.delta δB N=⋂i : Fin N,{x : Fin N → ℝ | x i∈Icc (-d.b-δB) B.delta} := by
        ext x; simp [preferredRightAngularBox]
      rw [he]
      exact isClosed_iInter (fun i => isClosed_Icc.preimage (continuous_apply i))
    have hi : ∀ᶠ x : Fin N → ℝ in 𝓝 θ,∀i,x i∈Ioo (-Real.pi-B.delta) (Real.pi-B.delta) := by
      apply Filter.eventually_all.mpr
      intro i
      exact (continuous_apply i).continuousAt.eventually (isOpen_Ioo.mem_nhds (hθ i))
    have hn : ∀ᶠ x : Fin N → ℝ in 𝓝 θ,x∉preferredRightAngularBox d B.delta δB N :=
      hc.isOpen_compl.mem_nhds hb
    apply fromzero
    filter_upwards [continuousAt_snd.tendsto.eventually (hn.and hi)] with z hz
    exact localizedPhysicalDensity_right_support σ d B τ rcut W hcut j z.1 z.2
      (fun i => ⟨(hz.2 i).1,(hz.2 i).2.le⟩) hz.1

end
end IsingBulk.HT22.Tail
