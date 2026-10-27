import IsingBulk.Preferred22.BumpExistence

/-! A genuine source bump below any prescribed positive analytic radius. -/
namespace IsingBulk.Preferred22
noncomputable section

def cappedPreferredDelta (d : PreferredBranchData) (cap : ℝ) : ℝ :=
  min (preferredBumpDelta d) (cap/2)

theorem cappedPreferredDelta_bounds (d : PreferredBranchData) {cap : ℝ} (hcap : 0 < cap) :
    0 < cappedPreferredDelta d cap ∧ cappedPreferredDelta d cap < cap ∧
      cappedPreferredDelta d cap ≤ preferredBumpDelta d := by
  exact ⟨lt_min (preferredBumpDelta_margins d).1 (half_pos hcap),
    (min_le_right _ _).trans_lt (half_lt_self hcap),min_le_left _ _⟩

def cappedCanonicalPreferredBump (d : PreferredBranchData) (cap : ℝ) (hcap : 0 < cap) :
    PreferredCoareaBump d where
  delta := cappedPreferredDelta d cap
  delta_pos := (cappedPreferredDelta_bounds d hcap).1
  delta_alpha := (cappedPreferredDelta_bounds d hcap).2.2.trans_lt
    (preferredBumpDelta_margins d).2.1
  delta_b := (cappedPreferredDelta_bounds d hcap).2.2.trans_lt
    (preferredBumpDelta_margins d).2.2.1
  delta_gap := (cappedPreferredDelta_bounds d hcap).2.2.trans_lt
    (preferredBumpDelta_margins d).2.2.2.1
  branch_plateau := by
    have h := (cappedPreferredDelta_bounds d hcap).2.2
    linarith [(preferredBumpDelta_margins d).2.2.2.2]
  p := sineCutoff (cappedPreferredDelta d cap)
  smooth := sineCutoff_smooth _
  periodic := sineCutoff_periodic _
  lower_bound := fun _ => Real.smoothTransition.nonneg _
  upper_bound := fun _ => Real.smoothTransition.le_one _
  upper_support := fun _ hθ hp => sineCutoff_upper_support
    (cappedPreferredDelta_bounds d hcap).1
    (by have h := (cappedPreferredDelta_bounds d hcap).2.2
        linarith [(preferredBumpDelta_margins d).2.1,d.alpha_lt,Real.pi_pos]) hθ hp
  plateau := fun _ hθ => sineCutoff_plateau
    (cappedPreferredDelta_bounds d hcap).1
    (by have h := (cappedPreferredDelta_bounds d hcap).2.2
        linarith [(preferredBumpDelta_margins d).2.1,d.alpha_lt,Real.pi_pos]) hθ

theorem cappedCanonicalPreferredBump_delta_lt (d : PreferredBranchData) {cap : ℝ}
    (hcap : 0 < cap) : (cappedCanonicalPreferredBump d cap hcap).delta < cap :=
  (cappedPreferredDelta_bounds d hcap).2.1

end
end IsingBulk.Preferred22
