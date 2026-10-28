import IsingBulk.HT22.Anchor.FixedFrameJets
namespace IsingBulk.HT22.Anchor
noncomputable section
open Set Filter Metric IsingBulk.Preferred22
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The explicit branch velocity correction has uniform scalar jets on a
single parameter neighborhood, independently of N and all cutoff cells. -/
theorem actual_branch_velocity_jets (d : PreferredBranchData) :
    ∃ ε₀ : ℝ,0<ε₀ ∧ ∀ j : ℕ,∃ C : ℝ,1≤C ∧ ∀ ε : ℝ,0<ε → ε<ε₀ →
      AnalyticAt ℂ (deriv preferredMovingBranch) (IsingBulk.Branch.radialParameter d.alpha ε) ∧
      ‖iteratedFDeriv ℂ j (deriv preferredMovingBranch)
        (IsingBulk.Branch.radialParameter d.alpha ε)‖≤C := by
  obtain ⟨ρ,hρ,hBa⟩ := Metric.eventually_nhds_iff.mp
    (preferredMovingBranch_analyticAt_reference d).eventually_analyticAt
  let K := closedBall (preferredSelectedPoint d) (ρ/2)
  have ha : AnalyticOnNhd ℂ (deriv preferredMovingBranch) K := by
    intro s hs
    apply AnalyticAt.deriv
    apply hBa
    have hh : dist s (preferredSelectedPoint d)≤ρ/2 := hs
    linarith
  refine ⟨ρ/2,half_pos hρ,?_⟩
  intro j
  obtain ⟨C,hC,hj⟩ := preferred_compact_scalar_all_jets _ K (isCompact_closedBall _ _) ha j
  refine ⟨C,hC,?_⟩
  intro ε hε hεr
  have hs : IsingBulk.Branch.radialParameter d.alpha ε∈K := by
    change dist _ _≤ρ/2
    rw [dist_eq_norm,preferred_radial_distance,abs_of_pos hε]
    exact hεr.le
  exact ⟨ha _ hs,hj _ hs⟩

/-- Bound for the correction in the literal shared source frame. -/
theorem branch_velocity_frame_bound {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (hp : ContDiff ℝ ∞ p) (hm : ContDiff ℝ ∞ m) (s : ℂ) (θ : Fin N → ℝ)
    (hpoint : PreferredFramePoint τ δ p m s θ) (hθ : ∀ i,θ i∈Ioo (-Real.pi-δ) δ)
    (xs : List (Option (Fin N))) (C : ℝ) (hC : 0≤C)
    (ha : AnalyticAt ℂ (deriv preferredMovingBranch) s)
    (hj : ‖iteratedFDeriv ℂ xs.length (deriv preferredMovingBranch) s‖≤C) :
    ‖preferredFrameJet τ p m (fun t _ => deriv preferredMovingBranch t) xs s θ‖≤C := by
  exact preferred_frame_analytic_projection_bound τ δ p m hp hm s θ hpoint hθ
    (deriv preferredMovingBranch) (deriv preferredMovingBranch)
    (ContinuousLinearMap.fst ℂ ℂ (Fin N → ℂ)) (fun z => norm_fst_le z)
    ha Filter.EventuallyEq.rfl xs C hC hj
end
end IsingBulk.HT22.Anchor
