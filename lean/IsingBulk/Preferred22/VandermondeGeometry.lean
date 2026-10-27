import IsingBulk.Preferred22.SourceVandermonde
import IsingBulk.Preferred22.SourceCollectiveNeighborhood
import IsingBulk.Preferred22.CollectiveAnalyticSource

/-! Genuine whole-right source geometry for the complete Vandermonde
recurrence, with one regime before derivative and particle orders. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Metric
open scoped BigOperators ContDiff Topology
set_option backward.isDefEq.respectTransparency false

theorem preferred_actual_vandermonde_geometry (d : PreferredBranchData) :
    ∃ cap : ℝ, 0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d, B.delta<cap →
      ∃ c δ ε₀ τ₀ δB : ℝ, 0<c ∧ 0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
        ∀ N : ℕ, 0<N → ∀ ε τ : ℝ, 0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
        ∀ θ : Fin N → ℝ,
        (∀ i, -δB≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta) →
        0<preferredAngularDiameter θ →
        let s := IsingBulk.Branch.radialParameter d.alpha ε
        let q := preferredSourceCoordinate τ B.p B.m s θ
        PreferredFramePoint τ δ B.p B.m s θ ∧
        (∀ i, θ i∈Ioo (-Real.pi-δ) δ) ∧
        AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => preferredResidualCollective z.1 z.2) (s,q) ∧
        (∀ i j, AnalyticAt ℂ
          (fun z : ℂ × (Fin N → ℂ) => preferredCollectiveDifferenceFactor z.1 z.2 i j) (s,q)) ∧
        (∀ i j, PreferredRightRegularPoint c s (q i) (q j)) := by
  obtain ⟨capG,ρ,c,D,hcapG,hcapGa,hρ,hc,hDc,hDv,hzero,hgood,hsource⟩ :=
    preferred_uniform_regular_source_domain d
  obtain ⟨capB,hcapB,hcapBa,hBn⟩ := preferred_actual_collective_neighborhood d
  obtain ⟨capC,hcapC,hcapCa,hCn⟩ := preferred_actual_collective_difference_neighborhood d
  refine ⟨min capG (min capB capC),lt_min hcapG (lt_min hcapB hcapC),
    (min_le_left _ _).trans_lt hcapGa,?_⟩
  intro B hBcap
  have hcaps : B.delta<capG ∧ B.delta<capB ∧ B.delta<capC := by
    simpa only [lt_min_iff] using hBcap
  obtain ⟨r,hr,himage⟩ := hsource B.p B.m B.smooth.continuous B.m_smooth.continuous
  obtain ⟨ηB,MB,εB,τB,δB₁,hηB,hMB,hεB,hτB,hδB₁,hδB₁B,hneighB⟩ := hBn B hcaps.2.1
  obtain ⟨ηC,MC,εC,τC,δB₂,hηC,hMC,hεC,hτC,hδB₂,hδB₂B,hneighC⟩ := hCn B hcaps.2.2
  obtain ⟨δ,εF,τF,hδ,hδa,hεF,hτF,hframe⟩ := preferred_actual_frame_points d B
  let ε₀ := min r (min (ρ/2) (min εB (min εC εF)))
  let τ₀ := min r (min τB (min τC τF))
  let δB := min (B.delta/2) (min (r/2) (min δB₁ δB₂))
  have hε₀ : 0<ε₀ := lt_min hr (lt_min (half_pos hρ) (lt_min hεB (lt_min hεC hεF)))
  have hτ₀ : 0<τ₀ := lt_min hr (lt_min hτB (lt_min hτC hτF))
  have hδB : 0<δB := lt_min (half_pos B.delta_pos) (lt_min (half_pos hr) (lt_min hδB₁ hδB₂))
  have hδs : δB≤B.delta/2 ∧ δB≤r/2 ∧ δB≤δB₁ ∧ δB≤δB₂ := by
    simpa only [δB,le_min_iff] using (le_rfl : δB≤min (B.delta/2) (min (r/2) (min δB₁ δB₂)))
  have hδBB : δB<B.delta := hδs.1.trans_lt (by linarith [B.delta_pos])
  refine ⟨c,δ,ε₀,τ₀,δB,hc,hε₀,hτ₀,hδB,hδBB,?_⟩
  intro N hN ε τ hε hεr hτ hτr θ hθ hdiam
  dsimp only
  have hes : ε<r ∧ ε<ρ/2 ∧ ε<εB ∧ ε<εC ∧ ε<εF := by
    simpa only [ε₀,lt_min_iff] using hεr
  have hts : τ<r ∧ τ<τB ∧ τ<τC ∧ τ<τF := by
    simpa only [τ₀,lt_min_iff] using hτr
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  let q := preferredSourceCoordinate τ B.p B.m s θ
  have hθB (i : Fin N) : -δB₁≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta :=
    ⟨(neg_le_neg hδs.2.2.1).trans (hθ i).1,(hθ i).2⟩
  have hθC (i : Fin N) : -δB₂≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta :=
    ⟨(neg_le_neg hδs.2.2.2).trans (hθ i).1,(hθ i).2⟩
  have hBa : AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => preferredResidualCollective z.1 z.2) (s,q) :=
    preferredResidualCollective_analyticAt_of_rescaled hN s q ηB (preferredAngularDiameter θ) hηB hdiam
      ((hneighB N hN ε τ hε hes.2.2.1 hτ hts.2.1 θ hθB hdiam).1 0 (by simp))
  have hCa (i j : Fin N) : AnalyticAt ℂ
      (fun z : ℂ × (Fin N → ℂ) => preferredCollectiveDifferenceFactor z.1 z.2 i j) (s,q) :=
    preferredCollectiveDifferenceFactor_analyticAt_of_rescaled hN s q i j ηC (preferredAngularDiameter θ) hηC hdiam
      ((hneighC N hN ε τ hε hes.2.2.2.1 hτ hts.2.2.1 θ hθC hdiam i j).1 0 (by simp))
  obtain ⟨hpoint,hθstrict⟩ := hframe δB hδB hδBB N hN ε τ hε hes.2.2.2.2 hτ hts.2.2.2 θ hθ
  have hq (i : Fin N) : q i∈D := by
    apply interior_subset
    have hpocc := preferred_occupancy_mean_mem hN B.p (fun x => ⟨B.lower_bound x,B.upper_bound x⟩) θ
    have hmocc := preferred_occupancy_mean_mem hN B.m (fun x => ⟨B.lower_bound (-x),B.upper_bound (-x)⟩) θ
    have hh := himage ε τ (occupancy B.p θ/(N:ℝ)) (occupancy B.m θ/(N:ℝ)) (θ i)
      (by simpa only [abs_of_pos hε] using hes.1)
      (by simpa only [abs_of_nonneg hτ] using hts.1) hpocc hmocc
      (by have hh := (hθ i).1; have hd := hδs.2.1; linarith)
      (by have hh := (hθ i).2; have hc := hcaps.1; linarith)
    rw [preferredBumpCoordinate_actual] at hh
    exact hh
  have hsρ : ‖s-preferredSelectedPoint d‖<ρ := by
    rw [preferred_radial_distance,abs_of_pos hε]
    linarith [hes.2.1]
  exact ⟨hpoint,hθstrict,hBa,hCa,fun i j => hgood s (q i) (q j) hsρ (hq i) (hq j)⟩

end
end IsingBulk.Preferred22
