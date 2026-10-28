import IsingBulk.HT22.Anchor.AmplitudeBall

namespace IsingBulk.HT22.Anchor
noncomputable section
open Set Filter Metric IsingBulk.Preferred22
open scoped Topology
set_option backward.isDefEq.respectTransparency false

theorem inverseGauge_analyticAt (s q : ℂ)
    (hB : AnalyticAt ℂ preferredMovingBranch s) :
    AnalyticAt ℂ (fun z : ℂ × ℂ => inverseGauge z.1 z.2) (s,q) := by
  have hb : AnalyticAt ℂ (fun z : ℂ × ℂ => preferredMovingBranch z.1) (s,q) :=
    AnalyticAt.comp (f := fun z : ℂ × ℂ => z.1) (g := preferredMovingBranch) hB analyticAt_fst
  exact ((analyticAt_const.mul (analyticAt_snd.add hb)).div_const).cexp

/-- The inverse gauge required by the odd bordered determinant has uniform
analytic balls on the actual complete one-sided source, before all N and jets. -/
theorem actual_source_gauge_balls (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧
      ∀ B : PreferredCoareaBump d,B.delta<cap → ∀ δB : ℝ,0<δB →
      ∃ ε₀ τ₀ η C : ℝ,0<ε₀ ∧ 0<τ₀ ∧ 0<η ∧ 1≤C ∧
      ∀ N : ℕ,0<N → ∀ ε τ : ℝ,0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
      ∀ θ : Fin N → ℝ,(∀ i,θ i∈Icc (-Real.pi-B.delta) B.delta) →
      let s := IsingBulk.Branch.radialParameter d.alpha ε
      let q := preferredSourceCoordinate τ B.p B.m s θ
      ∀ i, AnalyticOnNhd ℂ (fun z : ℂ × ℂ => inverseGauge z.1 z.2)
        (closedBall (s,q i) η) ∧
        ∀ z∈closedBall (s,q i) η,‖inverseGauge z.1 z.2‖≤C := by
  obtain ⟨cap,hcap,hcapa,hdom⟩ := preferred_actual_whole_inverse_partition d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB δB hδB
  obtain ⟨R,L,ρ,κ,εd,τd,c,hR,hL,hρ,hκ,hεd,hτd,_hc,hgood,hleft,hsource⟩ := hdom B hB δB hδB
  let D := R∪L
  let K := closedBall (preferredSelectedPoint d) (ρ/2) ×ˢ D
  have hK : IsCompact K := (isCompact_closedBall _ _).prod (hR.union hL)
  have hg : AnalyticOnNhd ℂ (fun z : ℂ × ℂ => inverseGauge z.1 z.2) K := by
    intro z hz
    have hs : ‖z.1-preferredSelectedPoint d‖<ρ := by
      have hh : ‖z.1-preferredSelectedPoint d‖≤ρ/2 := by
        simpa only [mem_closedBall,dist_eq_norm] using hz.1
      linarith
    apply inverseGauge_analyticAt
    rcases hz.2 with hq|hq
    · exact (hgood z.1 z.2 z.2 hs hq hq).1
    · exact (hleft z.1 z.2 hs hq).1
  obtain ⟨η,C,hη,hC,hballs⟩ := preferred_compact_analytic_balls _ K hK hg
  refine ⟨min εd (ρ/2),τd,η,C,lt_min hεd (half_pos hρ),hτd,hη,hC,?_⟩
  intro N hN ε τ hε hεr hτ hτr θ hθ
  dsimp only
  let s := IsingBulk.Branch.radialParameter d.alpha ε
  let q := preferredSourceCoordinate τ B.p B.m s θ
  have hs : ‖s-preferredSelectedPoint d‖≤ρ/2 := by
    rw [preferred_radial_distance,abs_of_pos hε]
    exact (hεr.trans_le (min_le_right _ _)).le
  intro i
  apply hballs
  refine ⟨by simpa only [mem_closedBall,dist_eq_norm] using hs,?_⟩
  rcases (hsource N hN ε τ hε (hεr.trans_le (min_le_left _ _)) hτ hτr θ hθ i).1 with h|h
  · exact Or.inl (h (mem_closedBall_self hκ.le))
  · exact Or.inr (h (mem_closedBall_self hκ.le))

end
end IsingBulk.HT22.Anchor
