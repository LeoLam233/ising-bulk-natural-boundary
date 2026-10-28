import IsingBulk.HT22.Kernel.FrameBound

namespace IsingBulk.HT22.Kernel
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Tail Geometry Set Filter
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem ordinary_frame_jets_on_domain {N : ℕ} (d : PreferredBranchData)
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
      (fun z : ℂ × ℂ × ℂ => ordinaryExtension z.1 z.2.1 z.2.2)
      (s,q+preferredMovingBranch s,r+preferredMovingBranch s)‖≤C) :
    ∀ i j, ‖frameJet τ p m
      (fun t x => sourceOrdinaryKernel τ p m t x i j) xs s θ‖≤C := by
  have hs' : ‖s-preferredSelectedPoint d‖<ρ := by linarith
  have hv (i : Fin N) : sourceCoordinate τ p m s θ i=
      preferredSourceCoordinate τ p m s θ i+preferredMovingBranch s :=
    sub_eq_iff_eq_add.mp (sourceCoordinate_moving_adapter τ p m s θ i)
  have hphase (i : Fin N) : regularPhase s (sourceCoordinate τ p m s θ i)=
      preferredRegularPhase s (preferredSourceCoordinate τ p m s θ i) := by
    rw [regularPhase,regularInverse_moving_adapter,sourceCoordinate_moving_adapter,hv]
    unfold preferredRegularPhase
    ring
  intro i j
  have hg : PreferredRightRegularPoint c s
      (sourceCoordinate τ p m s θ i-preferredMovingBranch s)
      (sourceCoordinate τ p m s θ j-preferredMovingBranch s) := by
    simpa only [sourceCoordinate_moving_adapter] using hgood s _ _ hs' (hq i) (hq j)
  have ha := ordinaryExtension_analyticAt c s _ _ hg
  have he := ordinaryScalar_germ c s _ _ hg
    (by rw [hphase]; exact hpoint.phase_im_neg i)
    (by rw [hphase]; exact hpoint.phase_im_neg j)
  have hb : ‖iteratedFDeriv ℂ xs.length
      (fun z : ℂ × ℂ × ℂ => ordinaryExtension z.1 z.2.1 z.2.2)
      (s,sourceCoordinate τ p m s θ i,sourceCoordinate τ p m s θ j)‖≤C := by
    rw [hv,hv]
    exact hK _ (hq i) _ (hq j)
  exact fixed_frame_analytic_projection_bound τ δ p m hp hm s θ hpoint hθ
    (fun z : ℂ × ℂ × ℂ => ordinaryScalar z.1 z.2.1 z.2.2)
    (fun z : ℂ × ℂ × ℂ => ordinaryExtension z.1 z.2.1 z.2.2)
    (preferredPairProjection i j) (preferredPairProjection_norm_le i j) ha he xs C hC hb

end
end IsingBulk.HT22.Kernel
