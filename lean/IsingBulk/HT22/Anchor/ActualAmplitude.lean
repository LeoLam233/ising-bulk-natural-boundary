import IsingBulk.HT22.Anchor.SourceGauge
namespace IsingBulk.HT22.Anchor
noncomputable section
open Set Filter Metric IsingBulk.Preferred22
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Actual odd bordered amplitude balls on the full anchored source. The scalar,
pair and gauge neighborhoods all precede the particle and derivative orders. -/
theorem actual_amplitude_balls (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d,B.delta<cap → ∀ δB : ℝ,0<δB →
      ∃ ε₀ τ₀ c A H : ℝ,0<ε₀ ∧ 0<τ₀ ∧ 0<c ∧ 0<A ∧ 0<H ∧
      ∀ N : ℕ,0<N → ∀ σ : ℂ,‖σ‖=1 → ∀ ε τ : ℝ,0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
      ∀ θ : Fin N → ℝ,(∀ i,θ i∈Icc (-Real.pi-B.delta) B.delta) →
      ∀ anchor : Fin N,θ anchor≤ -d.b-δB/2 →
      let s := IsingBulk.Branch.radialParameter d.alpha ε
      let q := preferredSourceCoordinate τ B.p B.m s θ
      ∃ F : (ℂ × (Fin N → ℂ)) → ℂ,
        (fun z : ℂ × (Fin N → ℂ) => amplitude σ z.1 z.2) =ᶠ[𝓝 (s,q)] F ∧
        AnalyticOnNhd ℂ F (closedBall (s,q) (c/(N:ℝ))) ∧
        ∀ z∈closedBall (s,q) (c/(N:ℝ)),‖F z‖≤H*(Real.sqrt (N+1:ℕ)*A^3)^(N+1)*A^N/(N.factorial:ℝ) := by
  obtain ⟨capS,hcapS,hcapSa,hscalar⟩ := preferred_actual_anchor_scalar_balls d
  obtain ⟨capK,hcapK,_hcapKa,hkernel⟩ := preferred_actual_anchor_kernel_representatives d
  obtain ⟨capG,hcapG,_hcapGa,hgauge⟩ := actual_source_gauge_balls d
  refine ⟨min capS (min capK capG),lt_min hcapS (lt_min hcapK hcapG),
    (min_le_left _ _).trans_lt hcapSa,?_⟩
  intro B hB δB hδB
  obtain ⟨εS,τS,ηS,CS,q₀,hεS,hτS,hηS,hCS,hq₀,hq₀1,hs⟩ :=
    hscalar B (hB.trans_le (min_le_left _ _)) δB hδB
  obtain ⟨εK,τK,ηK,CK,hεK,hτK,hηK,_hCK,hk⟩ :=
    hkernel B (hB.trans_le ((min_le_right _ _).trans (min_le_left _ _))) δB hδB
  obtain ⟨εG,τG,ηG,CG,hεG,hτG,hηG,_hCG,hg⟩ :=
    hgauge B (hB.trans_le ((min_le_right _ _).trans (min_le_right _ _))) δB hδB
  let η := min ηS (min ηK ηG)
  let C := max CS (max CK CG)
  have hη : 0<η := lt_min hηS (lt_min hηK hηG)
  have hC : 1≤C := hCS.trans (le_max_left _ _)
  have hCp : 0<C := lt_of_lt_of_le zero_lt_one hC
  obtain ⟨c,H,hc,hH,hball⟩ := amplitude_ball_of_data η C q₀ hη hC hq₀ hq₀1
  refine ⟨min εS (min εK εG),min τS (min τK τG),c,C,H,
    lt_min hεS (lt_min hεK hεG),lt_min hτS (lt_min hτK hτG),hc,hCp,hH,?_⟩
  intro N hN σ hσ ε τ hε hεr hτ hτr θ hθ anchor hanchor
  dsimp only
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  let q := preferredSourceCoordinate τ B.p B.m s θ
  obtain ⟨hsc,hgap⟩ := hs N hN ε τ hε (hεr.trans_le (min_le_left _ _))
    hτ (hτr.trans_le (min_le_left _ _)) θ hθ
  have hsd : PreferredAnchorScalarBallData s q η C := by
    intro i
    rcases hsc i with ⟨he,ha,hab,hz,hzb,hi,hn⟩
    refine ⟨he,ha.mono (closedBall_subset_closedBall (min_le_left _ _)),?_,
      hz.mono (closedBall_subset_closedBall (min_le_left _ _)),?_,hi.trans (le_max_left _ _),hn⟩
    · intro z hz'
      exact (hab z (closedBall_subset_closedBall (min_le_left _ _) hz')).trans (le_max_left _ _)
    · intro z hz'
      exact (hzb z (closedBall_subset_closedBall (min_le_left _ _) hz')).trans (le_max_left _ _)
  have hkd : PreferredAnchorPairBallData s q η C := by
    intro i j
    obtain ⟨G,he,ha,hb⟩ := hk N hN ε τ hε (hεr.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
      hτ (hτr.trans_le ((min_le_right _ _).trans (min_le_left _ _))) θ hθ i j
    refine ⟨G,he,ha.mono (closedBall_subset_closedBall ((min_le_right _ _).trans (min_le_left _ _))),?_⟩
    intro z hz
    exact (hb z (closedBall_subset_closedBall ((min_le_right _ _).trans (min_le_left _ _)) hz)).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hgd : ∀ i,AnalyticOnNhd ℂ (fun z : ℂ × ℂ => inverseGauge z.1 z.2)
      (closedBall (s,q i) η) ∧ ∀ z∈closedBall (s,q i) η,‖inverseGauge z.1 z.2‖≤C := by
    intro i
    obtain ⟨ha,hb⟩ := hg N hN ε τ hε
      (hεr.trans_le ((min_le_right _ _).trans (min_le_right _ _))) hτ
      (hτr.trans_le ((min_le_right _ _).trans (min_le_right _ _))) θ hθ i
    refine ⟨ha.mono (closedBall_subset_closedBall ((min_le_right _ _).trans (min_le_right _ _))),?_⟩
    intro z hz
    exact (hb z (closedBall_subset_closedBall ((min_le_right _ _).trans (min_le_right _ _)) hz)).trans
      ((le_max_right _ _).trans (le_max_right _ _))
  exact hball N hN σ hσ s q anchor hsd hkd hgd (hgap anchor hanchor)


end
end IsingBulk.HT22.Anchor
