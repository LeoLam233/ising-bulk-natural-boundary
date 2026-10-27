import IsingBulk.Preferred22.BumpExistence

/-! Genuine smooth periodic source bumps may be chosen after any positive
analytic-domain cap has been fixed. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set
open scoped ContDiff

theorem preferredCoareaBump_exists_below (d : PreferredBranchData)
    (cap : ℝ) (hcap : 0<cap) :
    ∃ B : PreferredCoareaBump d, B.delta<cap := by
  obtain ⟨hδ₀,hα,hb,hgap,hplateau⟩ := preferredBumpDelta_margins d
  let δ := min (preferredBumpDelta d) (cap/2)
  have hδ : 0<δ := lt_min hδ₀ (half_pos hcap)
  have hδ₀le : δ≤preferredBumpDelta d := min_le_left _ _
  have hδcap : δ<cap := (min_le_right _ _).trans_lt (by linarith)
  have hδα : δ<d.alpha/2 := hδ₀le.trans_lt hα
  have hδπ : δ<Real.pi/2 := by linarith [d.alpha_lt,Real.pi_pos]
  let B : PreferredCoareaBump d := {
    delta := δ
    delta_pos := hδ
    delta_alpha := hδα
    delta_b := hδ₀le.trans_lt hb
    delta_gap := hδ₀le.trans_lt hgap
    branch_plateau := by linarith
    p := sineCutoff δ
    smooth := sineCutoff_smooth δ
    periodic := sineCutoff_periodic δ
    lower_bound := fun θ => Real.smoothTransition.nonneg _
    upper_bound := fun θ => Real.smoothTransition.le_one _
    upper_support := fun θ hθ hp => sineCutoff_upper_support hδ hδπ hθ hp
    plateau := fun θ hθ => sineCutoff_plateau hδ hδπ hθ }
  exact ⟨B,hδcap⟩

end
end IsingBulk.Preferred22
