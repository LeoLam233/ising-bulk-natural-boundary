import IsingBulk.HT22.SeedFrameConversion.Bounds
import IsingBulk.Preferred22.SmoothMultiplierFrames
import IsingBulk.Preferred22.SourceFrameGeometry

/-! Actual fixed-N arbitrary smooth real angular weights in the new fixed-v
frame. Published generic smooth-frame estimates are converted exactly; no
analytic extension of the smooth weight or old collective endpoint is used. -/
namespace IsingBulk.HT22
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Tail IsingBulk.HT22.SeedFrameConversion Set Filter
open scoped BigOperators Topology ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem actual_smooth_weight_frame_jets (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧ ∀ B : PreferredCoareaBump d,B.delta<cap →
    ∃ ε₀ τ₀ δB : ℝ,0<ε₀ ∧ 0<τ₀ ∧ 0<δB ∧ δB<B.delta ∧
    ∀ N : ℕ,0<N → ∀ G : (Fin N → ℝ) → ℂ,ContDiff ℝ ∞ G →
    ∀ j : ℕ,∃ C : ℝ,0<C ∧ ∀ ε τ : ℝ,0<ε → ε<ε₀ → 0≤τ → τ<τ₀ →
    ∀ θ : Fin N → ℝ,(∀ i,-δB≤θ i+d.b ∧ θ i+d.b≤d.b+B.delta) →
    ∀ xs : List (Option (Fin N)),xs.length≤j →
    ‖frameJet τ B.p B.m (fun _ x => G x) xs (IsingBulk.Branch.radialParameter d.alpha ε) θ‖≤C := by
  obtain ⟨cap,hcap,hcapa,hweight⟩ := preferred_actual_smooth_angular_frame_jets d
  obtain ⟨rB,hrB,hBa⟩ := Metric.eventually_nhds_iff.mp
    (preferredMovingBranch_analyticAt_reference d).eventually_analyticAt
  let K := Metric.closedBall (preferredSelectedPoint d) (rB/2)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKa : ∀ t∈K,AnalyticAt ℂ preferredMovingBranch t := by
    intro t ht
    apply hBa
    have hh : dist t (preferredSelectedPoint d)≤rB/2 := ht
    linarith
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hB
  obtain ⟨eS,tS,dS,heS,htS,hdS,hdSB,hweight⟩ := hweight B hB
  obtain ⟨δ,eF,tF,_hδ,_hδa,heF,htF,hframe⟩ := preferred_actual_frame_points d B
  refine ⟨min eS (min eF (rB/2)),min tS tF,dS,
    lt_min heS (lt_min heF (half_pos hrB)),lt_min htS htF,hdS,hdSB,?_⟩
  intro N hN G hG j
  obtain ⟨A,hA,hAb⟩ := hweight N hN G hG j
  obtain ⟨C,hC,hCb⟩ := coefficients_compact_bound K hK hKa j
  refine ⟨((N:ℝ)+2)^j*(C*A),by positivity,?_⟩
  intro ε τ hε hεr hτ hτr θ hθ xs hxs
  have heS' := hεr.trans_le (min_le_left _ _)
  have heF' := hεr.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have heK := hεr.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have htS' := hτr.trans_le (min_le_left _ _)
  have htF' := hτr.trans_le (min_le_right _ _)
  obtain ⟨hpoint,hstrict⟩ := hframe dS hdS hdSB N hN ε τ hε heF' hτ htF' θ hθ
  let t := IsingBulk.Branch.radialParameter d.alpha ε
  have htK : t∈K := by
    change dist t (preferredSelectedPoint d)≤rB/2
    rw [dist_eq_norm,preferred_radial_distance,abs_of_pos hε]
    exact heK.le
  obtain ⟨Ω,hsub,hΩ,hz⟩ := mem_nhds_iff.mp
    (preferredFramePoint_eventually τ δ B.p B.m B.smooth B.m_smooth t θ hpoint hstrict)
  have hpoints : ∀ z∈Ω,PreferredFramePoint τ δ B.p B.m z.1 z.2 := fun z hz => hsub hz
  have hmix : PreferredMixedSmoothOn (fun z : ℂ × (Fin N → ℝ) => G z.2) Ω := by
    intro z _hz
    exact ⟨(hG.comp contDiff_snd).contDiffAt,by
      change DifferentiableAt ℂ (fun _ : ℂ => G z.2) z.1
      fun_prop⟩
  have hold (ys : List (Option (Fin N))) (hys : ys.length≤j) :
      ‖(1:ℂ)*preferredFrameJet τ B.p B.m (fun _ x => G x) ys t θ‖≤A := by
    simpa only [one_mul] using hAb ε τ hε heS' hτ htS' θ hθ ys hys
  simpa only [one_mul] using frameJet_bound_of_shared τ δ B.p B.m B.smooth B.m_smooth
    Ω hΩ hpoints (fun _ x => G x) hmix j C A (by linarith) hA.le 1 t θ hz
    (fun cs hcs => hCb cs hcs t htK) hold xs hxs

end
end IsingBulk.HT22
