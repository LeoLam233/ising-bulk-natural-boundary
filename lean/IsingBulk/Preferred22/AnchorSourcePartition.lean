import IsingBulk.Preferred22.AnchorSourceDomain

/-! The source partition of the full regular q domain. Every actual particle
has a fixed-radius right or damped-left complex neighborhood; a named
left anchor always has the damped-left neighborhood. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem preferred_actual_whole_inverse_partition (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d,B.delta<cap → ∀ δB : ℝ,0<δB →
      ∃ R L : Set ℂ,∃ ρ κ ε₀ τ₀ c : ℝ,
        IsCompact R ∧ IsCompact L ∧ 0<ρ ∧ 0<κ ∧ 0<ε₀ ∧ 0<τ₀ ∧ 0<c ∧
        (∀ s q r : ℂ,‖s-preferredSelectedPoint d‖<ρ → q∈R → r∈R →
          PreferredRightRegularPoint c s q r) ∧
        (∀ s q : ℂ,‖s-preferredSelectedPoint d‖<ρ → q∈L → PreferredLeftRegularPoint s q) ∧
        ∀ N : ℕ,0<N → ∀ ε τ : ℝ,0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
          ∀ θ : Fin N → ℝ,(∀ i,θ i∈Icc (-Real.pi-B.delta) B.delta) → ∀ i,
          (Metric.closedBall (preferredSourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ i) κ⊆R ∨
            Metric.closedBall (preferredSourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ i) κ⊆L) ∧
          (θ i≤ -d.b-δB/2 →
            Metric.closedBall (preferredSourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ i) κ⊆L) := by
  obtain ⟨cap,ρR,c,DR,hcap,hcapa,hρR,hc,hDR,_hconv,_hzero,hgoodR,hsourceR⟩ :=
    preferred_uniform_regular_source_domain_with_margin d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hBcap δB hδB
  obtain ⟨κR,rR,hκR,hrR,himageR⟩ := hsourceR B.p B.m B.smooth.continuous B.m_smooth.continuous
  let gap := Real.pi-B.delta-d.b
  have hgap : 0<gap := by dsimp [gap]; linarith [B.branch_plateau]
  let η := min (rR/4) (min (δB/4) (gap/4))
  have hη : 0<η := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hηR : η≤rR/4 := min_le_left _ _
  have hηB : η≤δB/4 := (min_le_right _ _).trans (min_le_left _ _)
  have hηg : η≤gap/4 := (min_le_right _ _).trans (min_le_right _ _)
  have hηgap : d.b+η<Real.pi-B.delta := by dsimp [gap] at hηg hgap; linarith
  obtain ⟨DL,ρL,hρL,hDL,hbaseL,hgoodL⟩ := preferred_compact_left_domain d B.delta_pos hη hηgap
  obtain ⟨κL,rL,hκL,hrL,himageL⟩ := preferred_physical_left_coordinate_image_margin d B.p B.m
    B.smooth.continuous B.m_smooth.continuous B.delta_pos hη hηgap DL hbaseL
  obtain ⟨δ,εf,τf,_hδ,_hδa,hεf,hτf,hframe⟩ := preferred_actual_whole_frame_points d B
  let ρ := min ρR ρL
  let κ := min κR κL
  let ε₀ := min rR (min rL εf)
  let τ₀ := min rR (min rL τf)
  refine ⟨DR,DL,ρ,κ,ε₀,τ₀,c,hDR,hDL,
    lt_min hρR hρL,lt_min hκR hκL,lt_min hrR (lt_min hrL hεf),
    lt_min hrR (lt_min hrL hτf),hc,?_,?_,?_⟩
  · intro s q r hs hq hr
    exact hgoodR s q r (hs.trans_le (min_le_left _ _)) hq hr
  · intro s q hs hq
    exact hgoodL s q (hs.trans_le (min_le_right _ _)) hq
  · intro N hN ε τ hε hεr hτ hτr θ hθ i
    have heR : ε<rR := hεr.trans_le (min_le_left _ _)
    have heL : ε<rL := hεr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have hef : ε<εf := hεr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have htR : τ<rR := hτr.trans_le (min_le_left _ _)
    have htL : τ<rL := hτr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
    have htf : τ<τf := hτr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hpocc := preferred_occupancy_mean_mem hN B.p (fun x => ⟨B.lower_bound x,B.upper_bound x⟩) θ
    have hmocc := preferred_occupancy_mean_mem hN B.m (fun x => ⟨B.lower_bound (-x),B.upper_bound (-x)⟩) θ
    have hpoint := (hframe N hN ε τ hε hef hτ htf θ hθ).1
    have hleft (hi : θ i≤ -d.b-η) :
        Metric.closedBall (preferredSourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ i) κL⊆DL := by
      have hh := himageL ε τ (occupancy B.p θ/(N:ℝ)) (occupancy B.m θ/(N:ℝ)) (θ i)
        (by simpa only [abs_of_pos hε] using heL)
        (by simpa only [abs_of_nonneg hτ] using htL) hpocc hmocc ⟨(hθ i).1,hi⟩
      rw [preferredPhysicalBumpCoordinate_actual d B.p B.m ε τ θ i (hpoint.upper i)] at hh
      exact hh
    constructor
    · by_cases hi : -d.b-rR≤θ i
      · left
        intro z hz
        have hh := himageR ε τ (occupancy B.p θ/(N:ℝ)) (occupancy B.m θ/(N:ℝ)) (θ i)
          (by simpa only [abs_of_pos hε] using heR)
          (by simpa only [abs_of_nonneg hτ] using htR) hpocc hmocc hi ((hθ i).2.trans hBcap.le)
        rw [preferredBumpCoordinate_actual] at hh
        exact hh (Metric.closedBall_subset_closedBall (show κ≤κR from min_le_left _ _) hz)
      · right
        intro z hz
        exact hleft (by linarith) (Metric.closedBall_subset_closedBall (show κ≤κL from min_le_right _ _) hz)
    · intro hi z hz
      exact hleft (by linarith) (Metric.closedBall_subset_closedBall (show κ≤κL from min_le_right _ _) hz)


end
end IsingBulk.Preferred22
