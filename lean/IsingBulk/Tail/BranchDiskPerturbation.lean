import IsingBulk.Analysis.BranchModulus
import IsingBulk.First.RadialDiskAdmissibility

/-! Parameter perturbations of the actual plateau dispersion retain the
real branch-center displacement. The perturbation is not set to zero and
no occupancy is held fixed during integration. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch

def diskBranchW (d : LocalBranchData) (ε t u : ℝ) (s : ℂ) : ℂ :=
  dispersion s (plateauY d.c₀ ε d.tau t d.thetaB u)

theorem diskBranchW_difference (d : LocalBranchData) (ε t u : ℝ) (s : ℂ) :
    diskBranchW d ε t u s-currentW d ε t u =
      (s+s⁻¹)-(radialParameter d.theta ε+(radialParameter d.theta ε)⁻¹) := by
  rw [currentW_dispersion]
  unfold diskBranchW dispersion
  ring

/-- A trace perturbation of size O(ε) preserves a uniform lower bound
O(|u|+ε+τt) for the actual branch distance. Constants precede all variables. -/
theorem disk_branch_distance (d : LocalBranchData) :
    ∃ c r : ℝ, 0 < c ∧ 0 < r ∧ ∀ ε t u : ℝ, ∀ s : ℂ,
      0 < ε → ε < r → 0 ≤ t → t < r → |u| < r →
      ‖(s+s⁻¹)-(radialParameter d.theta ε+(radialParameter d.theta ε)⁻¹)‖ ≤ c*ε →
      c*(|u|+ε+d.tau*t) ≤ ‖1-diskBranchW d ε t u s‖ := by
  obtain ⟨c,C,r,hc,_,hr,hmod⟩ := current_modulus_Q d
  refine ⟨c/2,r,half_pos hc,hr,?_⟩
  intro ε t u s hε hεr ht htr hur hs
  obtain ⟨hm,_⟩ := hmod ε t u hε hεr ht htr hur
  have hd : ‖(1-diskBranchW d ε t u s)-currentD d ε t u‖ ≤ c/2*ε := by
    rw [currentD, show (1-diskBranchW d ε t u s)-(1-currentW d ε t u) =
      -(diskBranchW d ε t u s-currentW d ε t u) by ring, norm_neg,
      diskBranchW_difference]
    exact hs
  have hn := norm_sub_norm_le (currentD d ε t u) (1-diskBranchW d ε t u s)
  have hn' : ‖currentD d ε t u‖ - ‖1-diskBranchW d ε t u s‖ ≤
      ‖(1-diskBranchW d ε t u s)-currentD d ε t u‖ := by
    simpa only [norm_sub_rev (currentD d ε t u)] using hn
  have hpos := mul_nonneg d.tau_pos.le ht
  nlinarith [hn', abs_nonneg u, mul_nonneg hc.le hpos, mul_nonneg hc.le (abs_nonneg u)]

/-- The same explicit trace perturbation preserves the designated upper-W
sheet. This is a separate obligation from pair continuity. -/
theorem disk_branch_imaginary_margin (d : LocalBranchData) :
    ∃ c r : ℝ, 0 < c ∧ 0 < r ∧ ∀ ε t u : ℝ, ∀ s : ℂ,
      0 < ε → ε < r → 0 ≤ t → t < r → |u| < r →
      ‖(s+s⁻¹)-(radialParameter d.theta ε+(radialParameter d.theta ε)⁻¹)‖ ≤ c*ε →
      c*(ε+d.tau*t) ≤ (diskBranchW d ε t u s).im := by
  obtain ⟨b,C,r,hb,_,hr,himag⟩ := current_imaginary_margin d
  refine ⟨b/2,r,half_pos hb,hr,?_⟩
  intro ε t u s hε hεr ht htr hur hs
  obtain ⟨hm,_⟩ := himag ε t u hε hεr ht htr hur
  have hd : ‖diskBranchW d ε t u s-currentW d ε t u‖ ≤ b/2*ε := by
    rw [diskBranchW_difference]; exact hs
  have hi := Complex.abs_im_le_norm (diskBranchW d ε t u s-currentW d ε t u)
  simp only [Complex.sub_im] at hi
  have hh := neg_le_abs ((diskBranchW d ε t u s).im-(currentW d ε t u).im)
  nlinarith [mul_nonneg hb.le (mul_nonneg d.tau_pos.le ht)]

/-- Conversion from a literal complex cε disk to trace slack, with one
constant fixed before ε, occupancy and angle. -/
theorem radial_trace_disk_slack (θ κ : ℝ) (hκ : 0 < κ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ s : ℂ,
      ‖s-radialParameter θ ε‖ ≤ δ*ε →
      ‖(s+s⁻¹)-(radialParameter θ ε+(radialParameter θ ε)⁻¹)‖ ≤ κ*ε := by
  let δ := min (1/4:ℝ) (κ/3)
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  refine ⟨δ,hδ,?_⟩
  intro ε hε hε1 s hs
  have ht : 1 ≤ ‖radialParameter θ ε‖ := by
    rw [IsingBulk.First.radialParameter_norm hε.le]; linarith
  have hsmall : ‖s-radialParameter θ ε‖ < 1/2 := by
    have hd1 : δ ≤ 1/4 := min_le_left _ _
    nlinarith
  have hsn := IsingBulk.First.norm_ge_half_of_near_unit ht hsmall
  have hb := IsingBulk.First.sourceS_sub_norm_le hsn ht
  change ‖(s+s⁻¹)-(radialParameter θ ε+(radialParameter θ ε)⁻¹)‖ ≤
    3*‖s-radialParameter θ ε‖ at hb
  have hdκ : δ ≤ κ/3 := min_le_right _ _
  nlinarith

/-- Actual branch distance on an original parameter disk. This statement
includes the complex parameter displacement in the exact dispersion. -/
theorem original_disk_branch_distance (d : LocalBranchData) :
    ∃ c δ r : ℝ, 0 < c ∧ 0 < δ ∧ 0 < r ∧ ∀ ε t u : ℝ, ∀ s : ℂ,
      0 < ε → ε < r → 0 ≤ t → t < r → |u| < r →
      ‖s-radialParameter d.theta ε‖ ≤ δ*ε →
      c*(|u|+ε+d.tau*t) ≤ ‖1-diskBranchW d ε t u s‖ := by
  obtain ⟨c,r,hc,hr,hm⟩ := disk_branch_distance d
  obtain ⟨δ,hδ,hd⟩ := radial_trace_disk_slack d.theta c hc
  refine ⟨c,δ,min r 1,hc,hδ,lt_min hr zero_lt_one,?_⟩
  intro ε t u s hε hεr ht htr hur hs
  exact hm ε t u s hε (hεr.trans_le (min_le_left _ _)) ht
    (htr.trans_le (min_le_left _ _)) (hur.trans_le (min_le_left _ _))
    (hd ε hε (hεr.le.trans (min_le_right _ _)) s hs)

def unitDeformationData (d : LocalBranchData) : LocalBranchData :=
  { d with tau := 1, tau_pos := zero_lt_one }

/-- Reparameterizing the radial displacement by τt makes the smallness
threshold precede the choice of τ. In particular t itself may range over
all of [0,1], as required for every occupancy and every λ. -/
theorem full_occupancy_disk_branch_distance (d : LocalBranchData) :
    ∃ c δ r : ℝ, 0 < c ∧ 0 < δ ∧ 0 < r ∧
    ∀ τ ε t u : ℝ, ∀ s : ℂ,
      0 ≤ τ → τ < r → 0 < ε → ε < r → 0 ≤ t → t ≤ 1 → |u| < r →
      ‖s-radialParameter d.theta ε‖ ≤ δ*ε →
      c*(|u|+ε+τ*t) ≤
        ‖1-dispersion s (plateauY d.c₀ ε τ t d.thetaB u)‖ := by
  obtain ⟨c,δ,r,hc,hδ,hr,hm⟩ := original_disk_branch_distance (unitDeformationData d)
  refine ⟨c,δ,r,hc,hδ,hr,?_⟩
  intro τ ε t u s hτ hτr hε hεr ht ht1 hur hs
  have hτt : 0 ≤ τ*t := mul_nonneg hτ ht
  have hτtr : τ*t < r := (mul_le_of_le_one_right hτ ht1).trans_lt hτr
  have hh := hm ε (τ*t) u s hε hεr hτt hτtr hur hs
  simpa [diskBranchW,unitDeformationData,plateauY,mul_assoc] using hh

end
end IsingBulk.Tail
