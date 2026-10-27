import IsingBulk.Preferred22.ShellObligations

/-! An explicit smooth periodic right telescope cutoff. Its return transition
is in the excluded upper plateau; the one-sided lift is retained exactly. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set
open scoped ContDiff

def preferredRightMargin (d : PreferredBranchData) (B : PreferredCoareaBump d) : ℝ :=
  min (B.delta/2) ((Real.pi-d.b-B.delta)/2)

theorem preferredRightMargin_bounds (d : PreferredBranchData) (B : PreferredCoareaBump d) :
    0 < preferredRightMargin d B ∧ preferredRightMargin d B < B.delta ∧
      d.b+preferredRightMargin d B < Real.pi-B.delta := by
  have hp : 0 < Real.pi-d.b-B.delta := by linarith [B.branch_plateau]
  have h1 : preferredRightMargin d B ≤ B.delta/2 := min_le_left _ _
  have h2 : preferredRightMargin d B ≤ (Real.pi-d.b-B.delta)/2 := min_le_right _ _
  refine ⟨lt_min (by linarith [B.delta_pos]) (by linarith),?_,?_⟩
  · linarith [B.delta_pos]
  · linarith

def preferredRightCutoff (d : PreferredBranchData) (δB θ : ℝ) : ℝ :=
  Real.smoothTransition ((Real.cos θ-Real.cos (d.b+δB))/
    (Real.cos (d.b+δB/2)-Real.cos (d.b+δB)))

theorem preferredRightCutoff_smooth (d : PreferredBranchData) (δB : ℝ) :
    ContDiff ℝ ∞ (preferredRightCutoff d δB) := by
  exact Real.smoothTransition.contDiff.comp (by fun_prop)

theorem preferredRightCutoff_periodic (d : PreferredBranchData) (δB : ℝ) :
    Function.Periodic (preferredRightCutoff d δB) (2*Real.pi) := by
  intro θ
  simp only [preferredRightCutoff,Real.cos_add_two_pi]

theorem preferredRightCutoff_den_pos (d : PreferredBranchData) {δB : ℝ}
    (hδ : 0 < δB) (hπ : d.b+δB < Real.pi) :
    0 < Real.cos (d.b+δB/2)-Real.cos (d.b+δB) := by
  apply sub_pos.mpr
  exact Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith [d.b_pos]) hπ.le (by linarith)

theorem preferredRightCutoff_zero (d : PreferredBranchData) (B : PreferredCoareaBump d)
    {δB θ : ℝ} (hδ : 0 < δB) (hgap : d.b+δB < Real.pi-B.delta)
    (hθ : θ ∈ Icc (-Real.pi-B.delta) B.delta) (hu : θ+d.b ≤ -δB) :
    preferredRightCutoff d δB θ=0 := by
  have hπ : d.b+δB < Real.pi := by linarith [B.delta_pos]
  have hc : Real.cos θ ≤ Real.cos (d.b+δB) := by
    by_cases hlo : -Real.pi ≤ θ
    · have h := Real.cos_le_cos_of_nonneg_of_le_pi
        (by linarith [d.b_pos] : 0 ≤ d.b+δB) (by linarith : -θ ≤ Real.pi)
        (by linarith : d.b+δB ≤ -θ)
      simpa only [Real.cos_neg] using h
    · have h := Real.cos_le_cos_of_nonneg_of_le_pi
        (by linarith [d.b_pos] : 0 ≤ d.b+δB)
        (by linarith : θ+2*Real.pi ≤ Real.pi)
        (by linarith [hθ.1] : d.b+δB ≤ θ+2*Real.pi)
      simpa only [Real.cos_add_two_pi] using h
  exact Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hc)
      (preferredRightCutoff_den_pos d hδ hπ).le)

theorem preferredRightCutoff_one (d : PreferredBranchData) (B : PreferredCoareaBump d)
    {δB θ : ℝ} (hδ : 0 < δB) (hgap : d.b+δB < Real.pi-B.delta)
    (hθ : θ ∈ Icc (-Real.pi-B.delta) B.delta) (hu : -δB/2 ≤ θ+d.b) :
    preferredRightCutoff d δB θ=1 := by
  have hπ : d.b+δB < Real.pi := by linarith [B.delta_pos]
  have hc : Real.cos (d.b+δB/2) ≤ Real.cos θ := by
    by_cases hlo : 0 ≤ θ
    · exact Real.cos_le_cos_of_nonneg_of_le_pi hlo (by linarith)
        (by linarith [hθ.2,B.delta_b,d.b_pos])
    · have h := Real.cos_le_cos_of_nonneg_of_le_pi (by linarith : 0 ≤ -θ)
        (by linarith : d.b+δB/2 ≤ Real.pi) (by linarith : -θ ≤ d.b+δB/2)
      simpa only [Real.cos_neg] using h
  apply Real.smoothTransition.one_of_one_le
  exact (le_div_iff₀ (preferredRightCutoff_den_pos d hδ hπ)).mpr (by linarith)

/-- Any smaller positive branch width is allowed, so the same actual cutoff
can meet the common-domain and finite-order mean-gap choices. -/
theorem preferred_right_cutoff_data_of_le (d : PreferredBranchData) (B : PreferredCoareaBump d)
    {δB : ℝ} (hδ : 0 < δB) (hle : δB ≤ preferredRightMargin d B) :
    PreferredRightCutoffData d B δB (preferredRightCutoff d δB) := by
  obtain ⟨_,hmargin,hgap'⟩ := preferredRightMargin_bounds d B
  have hδB : δB < B.delta := hle.trans_lt hmargin
  have hgap : d.b+δB < Real.pi-B.delta := by linarith
  refine ⟨hδ,hδB,preferredRightCutoff_smooth d _,preferredRightCutoff_periodic d _,?_,?_⟩
  · intro θ
    exact ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩
  · intro θ hθ
    exact ⟨preferredRightCutoff_zero d B hδ hgap hθ,
      preferredRightCutoff_one d B hδ hgap hθ⟩

/-- The precise right-cutoff existence obligation is proved constructively
by an explicit periodic expression, with no analytic cutoff assumption. -/
theorem preferred_right_cutoff_data (d : PreferredBranchData) (B : PreferredCoareaBump d) :
    PreferredRightCutoffData d B (preferredRightMargin d B)
      (preferredRightCutoff d (preferredRightMargin d B)) :=
  preferred_right_cutoff_data_of_le d B (preferredRightMargin_bounds d B).1 le_rfl

end
end IsingBulk.Preferred22
