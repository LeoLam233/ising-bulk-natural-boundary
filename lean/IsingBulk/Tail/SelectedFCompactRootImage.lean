import IsingBulk.Analysis.BranchData
import IsingBulk.Tail.SelectedFContinuationCompact
import IsingBulk.Tail.CompactRootGroups

/-! Physical attachment of the selected regular compact root image. The
actual radial source margin supplies the closed-lower-unit-disk geometry
needed for the two-group Schur suppression constants. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set

 theorem selectedLimitingShift_sine_nonpos (f : SelectorFunctions) {τ ρ θ : ℝ}
    (hτ : 0 ≤ τ) (hρ : 0 ≤ ρ) (hp : 0 ≤ f.p θ) (hm : 0 ≤ f.m θ)
    (hps : Real.sin θ ≤ 0 → f.p θ=0) (hms : 0 ≤ Real.sin θ → f.m θ=0) :
    selectedLimitingShift f τ ρ θ*Real.sin θ ≤ 0 := by
  by_cases hs : 0 ≤ Real.sin θ
  · have hv : selectedLimitingShift f τ ρ θ ≤ 0 := by
      simp only [selectedLimitingShift,hms hs,mul_zero,zero_div,add_zero]
      nlinarith
    exact mul_nonpos_of_nonpos_of_nonneg hv hs
  · have hs' := (lt_of_not_ge hs).le
    have hv : 0 ≤ selectedLimitingShift f τ ρ θ := by
      simp only [selectedLimitingShift,hps hs',mul_zero,zero_add]
      positivity
    exact mul_nonpos_of_nonneg_of_nonpos hv hs'

 theorem selectedCenterW_upper (theta c₀ : ℝ) (f : SelectorFunctions) {τ eps ρ u : ℝ}
    (hc₀ : 0 < c₀) (heps : 0 < eps) (hτ : 0 ≤ τ) (hρ : 0 ≤ ρ)
    (hmargin : (Real.exp (-c₀*eps))⁻¹-Real.exp (-c₀*eps) < (sourceS (radialParameter theta eps)).im)
    (hp : 0 ≤ f.p u) (hm : 0 ≤ f.m u)
    (hps : Real.sin u ≤ 0 → f.p u=0) (hms : 0 ≤ Real.sin u → f.m u=0) :
    0 < (selectedCenterW theta c₀ f τ eps ρ u).im := by
  have hr : 0 < Real.exp (-c₀*eps) := Real.exp_pos _
  have hr1 : Real.exp (-c₀*eps) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos hc₀ heps])
  have hy : ‖radialAnglePoint (-c₀*eps) u‖=Real.exp (-c₀*eps) := by
    simp [radialAnglePoint,Complex.norm_exp]
  have hb := sourceW_upper_of_margin hr hr1 hmargin hy
  have hs := selectedLimitingShift_sine_nonpos f hτ hρ hp hm hps hms
  exact hb.trans_le (radial_motion_im_mono (radialParameter theta eps) (-c₀*eps) u
    (selectedLimitingShift f τ ρ u) hs)

 theorem selected_regular_physical_compact (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) {η α τ : ℝ}
    (hη : 0 < η) (hηsmall : η ≤ Real.sin d.thetaB/4)
    (hα : 0 < α) (hαsmall : α < Real.sin d.thetaB/4)
    (hτ : 0 < τ) (hτsmall : 2*τ ≤ 1) (hτS : 4*τ < 1+Real.cos d.thetaB) :
    ∃ eps₀ : ℝ, 0 < eps₀ ∧ ∃ K : Set ℂ, IsCompact K ∧ K ⊆ continuedRootDomain ∧
      (∀ W ∈ K, 0 ≤ W.im) ∧ ∀ eps : ℝ, 0 < eps → eps < eps₀ →
        ∀ p ∈ selectedCompactParameters d.thetaB η,
          selectedCenterW d.theta d.c₀ (constructedSelector d.thetaB η α) τ eps p.1 p.2 ∈ K := by
  have hsinb : 0 < Real.sin d.thetaB := d.a_pos
  have hsint : 0 < Real.sin d.theta := Real.sin_pos_of_pos_of_lt_pi d.theta_pos
    (by linarith [Real.pi_pos,d.theta_lt])
  obtain ⟨epsA,hepsA,_hA1,K,hK,hKD,hcover⟩ := selected_regular_center_compact
    (c₀ := d.c₀) d.angle_relation hsinb hη hηsmall hα hαsmall hτ hτsmall hτS
  obtain ⟨epsR,hepsR,_hR1,hmarg⟩ := radialDampingMargin_linear hsint hcsmall
  refine ⟨min epsA epsR,lt_min hepsA hepsR,K ∩ {W : ℂ | 0 ≤ W.im},
    hK.inter_right (isClosed_le continuous_const Complex.continuous_im),
    fun W hW => hKD hW.1,fun _ hW => hW.2,?_⟩
  intro eps heps hepslt p hp
  refine ⟨hcover eps heps.le (hepslt.le.trans (min_le_left _ _)) p hp,?_⟩
  have hmargin : (Real.exp (-d.c₀*eps))⁻¹-Real.exp (-d.c₀*eps) <
      (sourceS (radialParameter d.theta eps)).im := by
    have hh := radialRadius_parameter_margin heps (hmarg eps heps (hepslt.trans_le (min_le_right _ _)))
    linarith [mul_pos hsint heps]
  apply (selectedCenterW_upper d.theta d.c₀ (constructedSelector d.thetaB η α)
    d.c₀_pos heps hτ.le hp.1.1 hmargin (thresholdStep_range _ _ _).1 (Real.smoothTransition.nonneg _) ?_ ?_).le
  · intro hs
    exact thresholdStep_zero (by linarith) (by linarith)
  · intro hs
    exact lowerM_zero_of_nonneg_sine d.thetaB η p.2 hsinb hη hηsmall hs

/-- The two-group suppression constants now come from an actual selected
compact source image, rather than from an assumed abstract root assignment. -/
 theorem selected_compact_root_groups (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) {η α τ : ℝ}
    (hη : 0 < η) (hηsmall : η ≤ Real.sin d.thetaB/4)
    (hα : 0 < α) (hαsmall : α < Real.sin d.thetaB/4)
    (hτ : 0 < τ) (hτsmall : 2*τ ≤ 1) (hτS : 4*τ < 1+Real.cos d.thetaB) :
    ∃ eps₀ : ℝ, 0 < eps₀ ∧ ∃ K : Set ℂ, IsCompact K ∧
      (∀ z ∈ K, ‖z‖ ≤ 1 ∧ z.im ≤ 0 ∧ z ≠ 1 ∧ z ≠ -1) ∧
      (∀ eps : ℝ, 0 < eps → eps < eps₀ → ∀ p ∈ selectedCompactParameters d.thetaB η,
        continuedRoot (selectedCenterW d.theta d.c₀ (constructedSelector d.thetaB η α) τ eps p.1 p.2) ∈ K) ∧
      ∃ g q : ℝ, 0 < g ∧ 0 < q ∧ q < 1 ∧
        (∀ z ∈ K, ‖z‖ ≤ 1-g ∨ z.im ≤ -g) ∧
        (∀ z ∈ K, ∀ w ∈ K,
          ((‖z‖ ≤ 1-g ∧ ‖w‖ ≤ 1-g) ∨ (z.im ≤ -g ∧ w.im ≤ -g)) → ‖pairKernel z w‖ ≤ q) ∧
        (∀ z ∈ K, ∀ w ∈ K, ‖pairKernel z w‖ ≤ 1) := by
  obtain ⟨eps₀,heps₀,K,hK,hKD,hKi,hcover⟩ :=
    selected_regular_physical_compact d hcsmall hη hηsmall hα hαsmall hτ hτsmall hτS
  let Z := continuedRoot '' K
  have hZ : IsCompact Z := hK.image_of_continuousOn
    (fun W hW => (continuedRoot_analyticAt (hKD hW)).continuousAt.continuousWithinAt)
  have hphys : ∀ z ∈ Z, ‖z‖ ≤ 1 ∧ z.im ≤ 0 ∧ z ≠ 1 ∧ z ≠ -1 := by
    rintro z ⟨W,hW,rfl⟩
    have hb := continuedRoot_closed_upper_bounds (hKD hW) (hKi W hW)
    have hn := continuedRoot_not_endpoints (hKD hW)
    exact ⟨hb.1,hb.2,hn.1,hn.2⟩
  obtain ⟨g,q,hg,hq,hq1,hgroups,hsame,hcross⟩ := compact_root_two_group_suppression Z hZ
    (fun z hz => (hphys z hz).1) (fun z hz => (hphys z hz).2.1)
    (fun z hz => (hphys z hz).2.2.1) (fun z hz => (hphys z hz).2.2.2)
  refine ⟨eps₀,heps₀,Z,hZ,hphys,?_,g,q,hg,hq,hq1,hgroups,hsame,hcross⟩
  intro eps heps hepslt p hp
  exact ⟨_,hcover eps heps hepslt p hp,rfl⟩

end
end IsingBulk.Tail
