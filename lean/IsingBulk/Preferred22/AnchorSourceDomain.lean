import IsingBulk.Preferred22.AnchorDomain
import IsingBulk.Preferred22.SourceFrameGeometry

/-! The actual full one-sided inverse domain, including compact left
particles and all right/branch particles, with a separate named-anchor
subdomain. Constants are chosen before particle number and derivative order. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter Metric
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem preferredBumpAngle_actual {N : ℕ} (p m : ℝ → ℝ) (τ : ℝ)
    (θ : Fin N → ℝ) (i : Fin N) :
    preferredBumpAngle m p τ (occupancy p θ/(N:ℝ)) (occupancy m θ/(N:ℝ)) (θ i)=
      deformedAngles τ p m θ i := by
  unfold preferredBumpAngle deformedAngles balancedShift
  push_cast
  ring

theorem preferredPhysicalBumpCoordinate_actual {N : ℕ} (d : PreferredBranchData)
    (p m : ℝ → ℝ) (ε τ : ℝ) (θ : Fin N → ℝ) (i : Fin N)
    (hW : 0<(temperatureTrace (IsingBulk.Branch.radialParameter d.alpha ε)-
      Complex.cos (deformedAngles τ p m θ i)).im) :
    preferredPhysicalBumpCoordinate d p m ε τ (occupancy p θ/(N:ℝ)) (occupancy m θ/(N:ℝ)) (θ i)=
      preferredSourceCoordinate τ p m (IsingBulk.Branch.radialParameter d.alpha ε) θ i := by
  rw [preferredPhysicalBumpCoordinate_eq,preferredBumpCoordinate_actual]
  simpa only [preferredBumpAngle_actual,preferredRadialTrace,temperatureTrace] using hW

/-- Genuine frames on every point of the complete lower physical period,
not only on the branch-side right cell. -/
theorem preferred_actual_whole_frame_points (d : PreferredBranchData) (B : PreferredCoareaBump d) :
    ∃ δ ε₀ τ₀ : ℝ,0<δ ∧ δ<d.alpha ∧ 0<ε₀ ∧ 0<τ₀ ∧
      ∀ N : ℕ,0<N → ∀ ε τ : ℝ,0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
      ∀ θ : Fin N → ℝ,(∀ i,θ i∈Icc (-Real.pi-B.delta) B.delta) →
      PreferredFramePoint τ δ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ ∧
        (∀ i,θ i∈Ioo (-Real.pi-δ) δ) := by
  let δ := (B.delta+d.alpha)/2
  have hδ : 0<δ := by dsimp [δ]; linarith [B.delta_pos,d.alpha_pos]
  have hδa : δ<d.alpha := by dsimp [δ]; linarith [B.delta_alpha,d.alpha_pos]
  have hBδ : B.delta<δ := by dsimp [δ]; linarith [B.delta_alpha,d.alpha_pos]
  obtain ⟨ε₀,hε₀,hmargin⟩ := preferred_radial_one_sided_margins d δ hδ hδa
  obtain ⟨τ₀,hτ₀,hM⟩ := preferred_bump_matrix_uniform d B
  refine ⟨δ,ε₀,τ₀,hδ,hδa,hε₀,hτ₀,?_⟩
  intro N hN ε τ hε hεr hτ hτr θ hθ
  obtain ⟨hSr,hSi,hSδ⟩ := hmargin ε hε hεr
  have hθ' (i : Fin N) : θ i∈Ioo (-Real.pi-δ) δ := by
    have hh := hθ i
    constructor <;> linarith [hh.1,hh.2]
  refine ⟨⟨hδ,hδa.trans d.alpha_lt,hSr,hSi,hSδ,
    fun i => ⟨(hθ' i).1.le,(hθ' i).2.le⟩,?_,hM N hN τ hτ hτr θ⟩,hθ'⟩
  intro i
  have hh := homotopy_complexW_im_pos hSi hτ (by norm_num : (0:ℝ)≤1) B.p B.m θ
    B.lower_bound (fun x => B.lower_bound (-x))
    (fun _ hx => B.p_zero_of_sin_nonpos hx) (fun _ hx => B.m_zero_of_sin_nonneg hx) i
  simpa only [complexW_homotopyRoot_eq] using hh

/-- One actual compact q domain covers every particle, and the named
anchor lies in a compact left subdomain with nonzero Uq and damping. -/
theorem preferred_actual_whole_inverse_domain (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d,B.delta<cap →
      ∀ δB : ℝ,0<δB →
      ∃ D L : Set ℂ,∃ ρ κ ε₀ τ₀ : ℝ,
        IsCompact D ∧ IsCompact L ∧ L⊆D ∧ 0<ρ ∧ 0<κ ∧ 0<ε₀ ∧ 0<τ₀ ∧
        (∀ s q : ℂ,‖s-preferredSelectedPoint d‖<ρ → q∈D →
          AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (s,q) ∧
          AnalyticAt ℂ (fun z : ℂ × ℂ => preferredOneBodyExtension z.1 z.2) (s,q)) ∧
        (∀ s q : ℂ,‖s-preferredSelectedPoint d‖<ρ → q∈L → PreferredLeftRegularPoint s q) ∧
        ∀ N : ℕ,0<N → ∀ ε τ : ℝ,0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
          ∀ θ : Fin N → ℝ,(∀ i,θ i∈Icc (-Real.pi-B.delta) B.delta) →
          ∀ i,Metric.closedBall (preferredSourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ i) κ⊆D ∧
            (θ i≤ -d.b-δB/2 →
              Metric.closedBall (preferredSourceCoordinate τ B.p B.m (IsingBulk.Branch.radialParameter d.alpha ε) θ i) κ⊆L) := by
  obtain ⟨cap,ρR,c,DR,hcap,hcapa,hρR,_hc,hDR,_hconv,_hzero,hgoodR,hsourceR⟩ :=
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
  refine ⟨DR∪DL,DL,ρ,κ,ε₀,τ₀,hDR.union hDL,hDL,subset_union_right,
    lt_min hρR hρL,lt_min hκR hκL,lt_min hrR (lt_min hrL hεf),lt_min hrR (lt_min hrL hτf),?_,?_,?_⟩
  · intro s q hs hq
    rcases hq with hq | hq
    · rcases hgoodR s q q (hs.trans_le (min_le_left _ _)) hq hq with
        ⟨hB,hU,_hU',_hcurv,_hcurv',_hcos,_hcos',hden,_hden',_hpair⟩
      exact ⟨hU,preferredOneBodyExtension_analyticAt s q hU hB hden⟩
    · rcases hgoodL s q (hs.trans_le (min_le_right _ _)) hq with ⟨hB,hU,_hq,_hc,hden,_hφ⟩
      exact ⟨hU,preferredOneBodyExtension_analyticAt s q hU hB hden⟩
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
    · intro z hz
      by_cases hi : -d.b-rR≤θ i
      · left
        have hh := himageR ε τ (occupancy B.p θ/(N:ℝ)) (occupancy B.m θ/(N:ℝ)) (θ i)
          (by simpa only [abs_of_pos hε] using heR)
          (by simpa only [abs_of_nonneg hτ] using htR) hpocc hmocc hi ((hθ i).2.trans hBcap.le)
        rw [preferredBumpCoordinate_actual] at hh
        exact hh (Metric.closedBall_subset_closedBall (show κ≤κR from min_le_left _ _) hz)
      · right
        exact hleft (by linarith) (Metric.closedBall_subset_closedBall (show κ≤κL from min_le_right _ _) hz)
    · intro hi z hz
      exact hleft (by linarith) (Metric.closedBall_subset_closedBall (show κ≤κL from min_le_right _ _) hz)

end
end IsingBulk.Preferred22
