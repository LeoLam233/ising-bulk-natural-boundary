import IsingBulk.HT22.Kernel.FrameBound
import IsingBulk.HT22.Tail.SourceCollision

/-! Joint fixed-v jets of the actual removable pair quotient, uniformly in N. -/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Kernel Set Metric
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem regularPairQuotient_analyticAt (c : ℝ) (t v w : ℂ)
    (h : PreferredRightRegularPoint c t (v-preferredMovingBranch t) (w-preferredMovingBranch t))
    (hww : PreferredRightRegularPoint c t (w-preferredMovingBranch t) (w-preferredMovingBranch t)) :
    AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => regularPairQuotient z.1 z.2.1 z.2.2) (t,v,w) := by
  have hB : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => preferredMovingBranch z.1) (t,v,w) :=
    AnalyticAt.comp (f := fun z : ℂ × ℂ × ℂ => z.1)
      (g := preferredMovingBranch) h.1 analyticAt_fst
  have hmap : AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ =>
      (z.1,z.2.1-preferredMovingBranch z.1,z.2.2-preferredMovingBranch z.1)) (t,v,w) :=
    analyticAt_fst.prod (((analyticAt_fst.comp analyticAt_snd).sub hB).prod
      ((analyticAt_snd.comp analyticAt_snd).sub hB))
  exact AnalyticAt.comp
    (f := fun z : ℂ × ℂ × ℂ =>
      (z.1,z.2.1-preferredMovingBranch z.1,z.2.2-preferredMovingBranch z.1))
    (g := fun z : ℂ × ℂ × ℂ => preferredKernelQuotient z.1 z.2.1 z.2.2)
    (preferredKernelQuotient_analyticAt _ _ _
      (preferredKernelExtension_analyticAt _ _ _ h.2.1 h.2.2.1 h.1 h.2.2.2.2.2.2.2.2.2)
      (preferredKernelExtension_analyticAt _ _ _ hww.2.1 hww.2.2.1 hww.1 hww.2.2.2.2.2.2.2.2.2)) hmap

theorem pairQuotient_fixed_domain_jets (d : PreferredBranchData) (ρ c : ℝ)
    (D : Set ℂ) (hρ : 0<ρ) (hD : IsCompact D) (hzero : (0:ℂ)∈D)
    (hgood : ∀ s q r : ℂ, ‖s-preferredSelectedPoint d‖<ρ → q∈D → r∈D →
      PreferredRightRegularPoint c s q r) :
    ∀ j : ℕ, ∃ C : ℝ, 0<C ∧ ∀ s q r : ℂ,
      ‖s-preferredSelectedPoint d‖≤ρ/2 → q∈D → r∈D →
      AnalyticAt ℂ (fun z : ℂ × ℂ × ℂ => regularPairQuotient z.1 z.2.1 z.2.2)
        (s,q+preferredMovingBranch s,r+preferredMovingBranch s) ∧
      ‖iteratedFDeriv ℂ j (fun z : ℂ × ℂ × ℂ => regularPairQuotient z.1 z.2.1 z.2.2)
        (s,q+preferredMovingBranch s,r+preferredMovingBranch s)‖≤C := by
  let K := pairShiftImage (preferredSelectedPoint d) (ρ/2) D
  have hB : ∀ s∈closedBall (preferredSelectedPoint d) (ρ/2),
      AnalyticAt ℂ preferredMovingBranch s := by
    intro s hs
    have hdist : ‖s-preferredSelectedPoint d‖≤ρ/2 := by
      simpa only [mem_closedBall,dist_eq_norm] using hs
    exact (hgood s 0 0 (by linarith) hzero hzero).1
  have hK : IsCompact K := pairShiftImage_compact _ _ _ hD hB
  have ha : AnalyticOnNhd ℂ
      (fun z : ℂ × ℂ × ℂ => regularPairQuotient z.1 z.2.1 z.2.2) K := by
    rintro z ⟨⟨s,q,r⟩,⟨hs,hq,hr⟩,rfl⟩
    have hdist : ‖s-preferredSelectedPoint d‖≤ρ/2 := by
      simpa only [mem_closedBall,dist_eq_norm] using hs
    apply regularPairQuotient_analyticAt c
    · simpa only [add_sub_cancel_right] using hgood s q r (by linarith) hq hr
    · simpa only [add_sub_cancel_right] using hgood s r r (by linarith) hr hr
  intro j
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn (fun z hz =>
    ((ha.iteratedFDeriv j) z hz).continuousAt.continuousWithinAt)
  refine ⟨max C 0+1,by positivity,?_⟩
  intro s q r hs hq hr
  have hm : (s,q+preferredMovingBranch s,r+preferredMovingBranch s)∈K :=
    ⟨(s,q,r),⟨by simpa only [mem_closedBall,dist_eq_norm] using hs,hq,hr⟩,rfl⟩
  exact ⟨ha _ hm,(hC _ hm).trans (by have := le_max_left C 0;linarith)⟩

theorem pairQuotient_frame_jets_on_domain {N : ℕ} (d : PreferredBranchData)
    (ρ c : ℝ) (D : Set ℂ) (hρ : 0<ρ)
    (hgood : ∀ s q r : ℂ, ‖s-preferredSelectedPoint d‖<ρ → q∈D → r∈D →
      PreferredRightRegularPoint c s q r)
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m)
    (s : ℂ) (θ : Fin N → ℝ) (hpoint : PreferredFramePoint τ δ p m s θ)
    (hθ : ∀ i, θ i∈Ioo (-Real.pi-δ) δ)
    (hs : ‖s-preferredSelectedPoint d‖≤ρ/2)
    (hq : ∀ i, preferredSourceCoordinate τ p m s θ i∈D)
    (xs : List (Option (Fin N))) (C : ℝ) (hC : 0≤C)
    (hK : ∀ q∈D, ∀ r∈D, ‖iteratedFDeriv ℂ xs.length
      (fun z : ℂ × ℂ × ℂ => regularPairQuotient z.1 z.2.1 z.2.2)
      (s,q+preferredMovingBranch s,r+preferredMovingBranch s)‖≤C) :
    ∀ i j, ‖frameJet τ p m
      (fun t x => preferredSourceKernelQuotient τ p m t x i j) xs s θ‖≤C := by
  have hs' : ‖s-preferredSelectedPoint d‖<ρ := by linarith
  have hv (i : Fin N) : sourceCoordinate τ p m s θ i=
      preferredSourceCoordinate τ p m s θ i+preferredMovingBranch s :=
    sub_eq_iff_eq_add.mp (sourceCoordinate_moving_adapter τ p m s θ i)
  intro i j
  have hg : PreferredRightRegularPoint c s
      (sourceCoordinate τ p m s θ i-preferredMovingBranch s)
      (sourceCoordinate τ p m s θ j-preferredMovingBranch s) := by
    simpa only [sourceCoordinate_moving_adapter] using hgood s _ _ hs' (hq i) (hq j)
  have hgg : PreferredRightRegularPoint c s
      (sourceCoordinate τ p m s θ j-preferredMovingBranch s)
      (sourceCoordinate τ p m s θ j-preferredMovingBranch s) := by
    simpa only [sourceCoordinate_moving_adapter] using hgood s _ _ hs' (hq j) (hq j)
  have ha := regularPairQuotient_analyticAt c s _ _ hg hgg
  have hb : ‖iteratedFDeriv ℂ xs.length
      (fun z : ℂ × ℂ × ℂ => regularPairQuotient z.1 z.2.1 z.2.2)
      (s,sourceCoordinate τ p m s θ i,sourceCoordinate τ p m s θ j)‖≤C := by
    rw [hv,hv]
    exact hK _ (hq i) _ (hq j)
  have hh := fixed_frame_analytic_projection_bound τ δ p m hp hm s θ hpoint hθ
    (fun z : ℂ × ℂ × ℂ => regularPairQuotient z.1 z.2.1 z.2.2)
    (fun z : ℂ × ℂ × ℂ => regularPairQuotient z.1 z.2.1 z.2.2)
    (preferredPairProjection i j) (preferredPairProjection_norm_le i j) ha (Filter.EventuallyEq.refl _ _) xs C hC hb
  change ‖frameJet τ p m (fun t x => regularPairQuotient t
    (sourceCoordinate τ p m t x i) (sourceCoordinate τ p m t x j)) xs s θ‖≤C at hh
  simpa only [sourcePairQuotient_eq_shared] using hh

end
end IsingBulk.HT22.Tail
