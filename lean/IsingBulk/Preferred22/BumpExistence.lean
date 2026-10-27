import IsingBulk.Preferred22.Coarea
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-! A concrete periodic C-infinity bump satisfying the Preferred source
requirements, with a strictly positive endpoint support margin. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped ContDiff
open Set

theorem preferred_branch_lt_twice_alpha (d : PreferredBranchData) : d.b < 2*d.alpha := by
  have hc0 : 0 < Real.cos d.alpha := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [d.alpha_pos,Real.pi_pos],d.alpha_lt⟩
  have hc1 : Real.cos d.alpha < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0:ℝ) ≤ 0)
      (by linarith [d.alpha_lt,Real.pi_pos] : d.alpha ≤ Real.pi) d.alpha_pos
    simpa only [Real.cos_zero] using h
  have hcos : Real.cos (2*d.alpha) < Real.cos d.b := by
    rw [Real.cos_two_mul,d.angle_relation]
    nlinarith [mul_pos hc0 (sub_pos.mpr hc1)]
  by_contra h
  have hle := Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [d.alpha_pos] : 0 ≤ 2*d.alpha)
    d.b_lt.le (le_of_not_gt h)
  linarith

def preferredBumpDelta (d : PreferredBranchData) : ℝ :=
  min (d.alpha/4) (min (d.b/4) (min ((2*d.alpha-d.b)/4) ((Real.pi-d.b)/2)))

theorem preferredBumpDelta_margins (d : PreferredBranchData) :
    0 < preferredBumpDelta d ∧ preferredBumpDelta d < d.alpha/2 ∧
      preferredBumpDelta d < d.b/2 ∧ preferredBumpDelta d < (2*d.alpha-d.b)/2 ∧
      d.b < Real.pi-preferredBumpDelta d := by
  have hgap : 0 < 2*d.alpha-d.b := sub_pos.mpr (preferred_branch_lt_twice_alpha d)
  have hend : 0 < Real.pi-d.b := sub_pos.mpr d.b_lt
  have hδ0 : 0 < preferredBumpDelta d := by
    unfold preferredBumpDelta
    have := d.alpha_pos
    have := d.b_pos
    positivity
  have h1 : preferredBumpDelta d ≤ d.alpha/4 := min_le_left _ _
  have h2 : preferredBumpDelta d ≤ d.b/4 := (min_le_right _ _).trans (min_le_left _ _)
  have h3 : preferredBumpDelta d ≤ (2*d.alpha-d.b)/4 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have h4 : preferredBumpDelta d ≤ (Real.pi-d.b)/2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  exact ⟨hδ0,by linarith [d.alpha_pos],by linarith [d.b_pos],by linarith,by linarith⟩

def sineCutoff (δ θ : ℝ) : ℝ := Real.smoothTransition (2*Real.sin θ/Real.sin δ-1)

theorem sineCutoff_smooth (δ : ℝ) : ContDiff ℝ ∞ (sineCutoff δ) := by
  unfold sineCutoff
  exact Real.smoothTransition.contDiff.comp (by fun_prop)

theorem sineCutoff_periodic (δ : ℝ) : Function.Periodic (sineCutoff δ) (2*Real.pi) := by
  intro θ
  unfold sineCutoff
  rw [Real.sin_add_two_pi]

theorem sineCutoff_sine_margin {δ θ : ℝ} (hδ : 0 < δ) (hδπ : δ < Real.pi/2)
    (hp : sineCutoff δ θ ≠ 0) : Real.sin δ < 2*Real.sin θ := by
  have hs : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])
  have harg : 0 < 2*Real.sin θ/Real.sin δ-1 := by
    by_contra h
    exact hp (Real.smoothTransition.zero_of_nonpos (le_of_not_gt h))
  have hq : 1 < 2*Real.sin θ/Real.sin δ := by linarith
  simpa only [one_mul] using (lt_div_iff₀ hs).mp hq

theorem sineCutoff_upper_support {δ θ : ℝ} (hδ : 0 < δ) (hδπ : δ < Real.pi/2)
    (hθ : θ ∈ Icc (-Real.pi) Real.pi) (hp : sineCutoff δ θ ≠ 0) : θ ∈ Ioo 0 Real.pi := by
  have hsδ : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])
  have hsθ : 0 < Real.sin θ := by linarith [sineCutoff_sine_margin hδ hδπ hp]
  constructor
  · by_contra h
    have hs := Real.sin_nonpos_of_nonpos_of_neg_pi_le (le_of_not_gt h) hθ.1
    linarith
  · by_contra h
    have he : θ = Real.pi := le_antisymm hθ.2 (le_of_not_gt h)
    rw [he,Real.sin_pi] at hsθ
    linarith

theorem sineCutoff_plateau {δ θ : ℝ} (hδ : 0 < δ) (hδπ : δ < Real.pi/2)
    (hθ : θ ∈ Icc δ (Real.pi-δ)) : sineCutoff δ θ = 1 := by
  have hsδ : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])
  have hsin : Real.sin δ ≤ Real.sin θ := by
    by_cases hhalf : θ ≤ Real.pi/2
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hhalf hθ.1
    · have h := Real.sin_le_sin_of_le_of_le_pi_div_two
        (by linarith [Real.pi_pos] : -(Real.pi/2) ≤ δ)
        (by linarith : Real.pi-θ ≤ Real.pi/2) (by linarith [hθ.2] : δ ≤ Real.pi-θ)
      simpa only [Real.sin_pi_sub] using h
  have hq : 2 ≤ 2*Real.sin θ/Real.sin δ :=
    (le_div_iff₀ hsδ).mpr (by linarith)
  exact Real.smoothTransition.one_of_one_le (by linarith)

/-- An explicit genuine source bump; no analytic-cutoff or coarea conclusion
is assumed in this construction. -/
def canonicalPreferredBump (d : PreferredBranchData) : PreferredCoareaBump d where
  delta := preferredBumpDelta d
  delta_pos := (preferredBumpDelta_margins d).1
  delta_alpha := (preferredBumpDelta_margins d).2.1
  delta_b := (preferredBumpDelta_margins d).2.2.1
  delta_gap := (preferredBumpDelta_margins d).2.2.2.1
  branch_plateau := (preferredBumpDelta_margins d).2.2.2.2
  p := sineCutoff (preferredBumpDelta d)
  smooth := sineCutoff_smooth _
  periodic := sineCutoff_periodic _
  lower_bound := fun θ => Real.smoothTransition.nonneg _
  upper_bound := fun θ => Real.smoothTransition.le_one _
  upper_support := fun θ hθ hp => sineCutoff_upper_support (preferredBumpDelta_margins d).1
    (by linarith [(preferredBumpDelta_margins d).2.1,d.alpha_lt,Real.pi_pos]) hθ hp
  plateau := fun θ hθ => sineCutoff_plateau (preferredBumpDelta_margins d).1
    (by linarith [(preferredBumpDelta_margins d).2.1,d.alpha_lt,Real.pi_pos]) hθ

theorem preferredCoareaBump_nonempty (d : PreferredBranchData) : Nonempty (PreferredCoareaBump d) :=
  ⟨canonicalPreferredBump d⟩

/-- Positive distance of the actual bump support from both semicircle
endpoints, as required for the selected branch-population estimates. -/
theorem sineCutoff_endpoint_margin {δ θ : ℝ} (hδ : 0 < δ) (hδπ : δ < Real.pi/2)
    (hθ : θ ∈ Icc (-Real.pi) Real.pi) (hp : sineCutoff δ θ ≠ 0) :
    Real.sin δ/4 ≤ θ ∧ θ ≤ Real.pi-Real.sin δ/4 := by
  have hsδ : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])
  have hpos := sineCutoff_upper_support hδ hδπ hθ hp
  have hmargin := sineCutoff_sine_margin hδ hδπ hp
  have hlo := Real.sin_le hpos.1.le
  have hhi := Real.sin_le (sub_nonneg.mpr hpos.2.le)
  rw [Real.sin_pi_sub] at hhi
  constructor <;> linarith

theorem canonicalPreferredBump_support_margin (d : PreferredBranchData) :
    ∃ η : ℝ, 0 < η ∧ ∀ θ ∈ Icc (-Real.pi) Real.pi,
      (canonicalPreferredBump d).p θ ≠ 0 → θ ∈ Icc η (Real.pi-η) := by
  obtain ⟨hδ,hα,_,_,_⟩ := preferredBumpDelta_margins d
  have hδπ : preferredBumpDelta d < Real.pi/2 := by linarith [d.alpha_lt,Real.pi_pos]
  refine ⟨Real.sin (preferredBumpDelta d)/4,?_,?_⟩
  · exact div_pos (Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])) (by norm_num)
  · intro θ hθ hp
    exact sineCutoff_endpoint_margin hδ hδπ hθ hp

end
end IsingBulk.Preferred22
