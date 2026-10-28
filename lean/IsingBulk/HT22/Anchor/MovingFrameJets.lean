import IsingBulk.HT22.Anchor.AmplitudeJets
namespace IsingBulk.HT22.Anchor
noncomputable section
open Set Filter Metric IsingBulk.Preferred22
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Bounds in the shared moving-q frame, explicitly labeled. Fixed-v
transport requires the branch-velocity correction and is not inferred here. -/
theorem actual_amplitude_moving_frame_jets (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d,B.delta<cap → ∀ δB : ℝ,0<δB →
      ∃ ε₀ τ₀ : ℝ,0<ε₀ ∧ 0<τ₀ ∧
      ∀ J : ℕ,∃ C : ℝ,1≤C ∧
      ∀ N : ℕ,0<N → ∀ σ : ℂ,‖σ‖=1 → ∀ ε τ : ℝ,0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
      ∀ θ : Fin N → ℝ,(∀ i,θ i∈Icc (-Real.pi-B.delta) B.delta) →
      ∀ anchor : Fin N,θ anchor≤ -d.b-δB/2 →
      ∀ xs : List (Option (Fin N)),xs.length≤J →
      ‖preferredFrameJet τ B.p B.m
        (fun t x => amplitude σ t (preferredSourceCoordinate τ B.p B.m t x)) xs
        (IsingBulk.Branch.radialParameter d.alpha ε) θ‖≤(C/Real.sqrt N)^N*(N:ℝ)^(J+1) := by
  obtain ⟨cap,hcap,hcapa,hsource⟩ := actual_amplitude_jets d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB δB hδB
  obtain ⟨εa,τa,hεa,hτa,hjets⟩ := hsource B hB δB hδB
  obtain ⟨δ,εf,τf,_hδ,_hδa,hεf,hτf,hframe⟩ := preferred_actual_whole_frame_points d B
  refine ⟨min εa εf,min τa τf,lt_min hεa hεf,lt_min hτa hτf,?_⟩
  intro J
  obtain ⟨C,hC,hjet⟩ := hjets J
  refine ⟨C,hC,?_⟩
  intro N hN σ hσ ε τ hε hεr hτ hτr θ hθ anchor hanchor xs hxs
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  obtain ⟨hpoint,hstrict⟩ := hframe N hN ε τ hε (hεr.trans_le (min_le_right _ _))
    hτ (hτr.trans_le (min_le_right _ _)) θ hθ
  obtain ⟨ha,hb⟩ := hjet N hN σ hσ ε τ hε (hεr.trans_le (min_le_left _ _))
    hτ (hτr.trans_le (min_le_left _ _)) θ hθ anchor hanchor
  exact preferred_frame_analytic_projection_bound τ δ B.p B.m B.smooth B.m_smooth s θ hpoint hstrict
    (fun z : ℂ × (Fin N → ℂ) => amplitude σ z.1 z.2)
    (fun z : ℂ × (Fin N → ℂ) => amplitude σ z.1 z.2)
    (ContinuousLinearMap.id ℂ (ℂ × (Fin N → ℂ))) (fun _ => le_rfl) ha Filter.EventuallyEq.rfl xs
    ((C/Real.sqrt N)^N*(N:ℝ)^(J+1)) (by have hCp := zero_le_one.trans hC; positivity) (hb xs.length hxs)

end
end IsingBulk.HT22.Anchor
