import IsingBulk.Tail.MixedCoefficientBounds

/-! Actual normalized mixed residual input on literal nested cutoff jets.
The compact coefficient core is evaluated at source-derived bounded data. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set
open scoped BigOperators Topology

def mixedBranchIndexSet {N : ℕ} (sigma : Fin N → Fin 3) : Finset (Fin N) :=
  Finset.univ.filter (fun i => sigma i=2)

theorem sector_branch_label_profile {b inner θ : ℝ} (hi : 0< inner)
    (hθ : θ ∈ tsupport (sectorLabel b inner hi 2)) : |sectorDisplacement b θ|≤ inner := by
  have he : sectorLabel b inner hi (2:Fin 3)=sectorBranch b inner hi := by funext x; simp [sectorLabel]
  rw [he] at hθ
  exact (sector_labels_tsupport b inner hi).2.2 hθ

theorem sector_compact_label_profile {b inner θ : ℝ} (hi : 0< inner) (label : Fin 3)
    (hl : label≠2) (hθ : θ ∈ tsupport (sectorLabel b inner hi label)) :
    inner/2≤|sectorDisplacement b θ| := by
  have hc : label=0 ∨ label=1 := by omega
  rcases hc with rfl | rfl
  · have he : sectorLabel b inner hi (0:Fin 3)=sectorLeft b inner hi := by funext x; simp [sectorLabel]
    rw [he] at hθ
    exact ((sector_labels_tsupport b inner hi).1 hθ).trans (le_abs_self _)
  · have he : sectorLabel b inner hi (1:Fin 3)=sectorRight b inner hi := by funext x; simp [sectorLabel]
    rw [he] at hθ
    have hh := (sector_labels_tsupport b inner hi).2.1 hθ
    change sectorDisplacement b θ≤ -inner/2 at hh
    exact (show inner/2≤-sectorDisplacement b θ by linarith).trans (neg_le_abs _)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1500000 in
theorem mixed_actual_nested_residual_data (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (outer : ℝ) (ho : 0<outer) :
    ∃ (inner : ℝ) (hi : 0< inner) (c e t₀ B : ℝ), inner≤ outer/4 ∧ 0<c ∧ 0<e ∧ 0<t₀ ∧ 0<B ∧
      ∀ η α : ℝ, 0<η → η≤ Real.sin d.thetaB/4 → 0<α →
      ∀ (N : ℕ) (eps τ lam : ℝ) (θ : Fin N → ℝ) (j q : Fin N)
        (sigma : Fin N → Fin 3) (l : List (Fin N)) (s : ℂ),
        1≤ N → 0<eps → eps<e → 0≤τ → 0≤ lam → lam≤1 → lam*τ<t₀ → sigma j=2 →
        θ ∈ tsupport (IsingBulk.Jets.cutoffJet l (nestedSectorWeight d.thetaB outer inner ho hi q sigma)) →
        ‖s-radialParameter d.theta eps‖≤ c*eps →
        actualMixedResidualData (mixedBranchIndexSet sigma) j q s
          (deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam θ)
          ∈ mixedResidualCompact B := by
  obtain ⟨iS,cS,eS,tS,hiS,hioS,hcS,heS,htS,hSlope⟩ := mixed_actual_profile_slope_separation d hcsmall outer ho
  let inner := min iS (min 1 ((Real.sin d.thetaB)^2/4))
  have hi : 0< inner := lt_min hiS (lt_min zero_lt_one (by positivity [d.a_pos]))
  have hiS' : inner≤ iS := min_le_left _ _
  have hi1 : inner≤1 := (min_le_right _ _).trans (min_le_left _ _)
  have his : inner≤(Real.sin d.thetaB)^2/4 := (min_le_right _ _).trans (min_le_right _ _)
  have hio : inner≤ outer/4 := hiS'.trans hioS
  obtain ⟨cB,eB,tB,B,hcB,heB,htB,hB,hCoeff⟩ := mixed_actual_profile_coefficient_bounds d hcsmall inner hi hi1 his
  let c := min cS cB
  refine ⟨inner,hi,c,min eS eB,min tS tB,B,hio,lt_min hcS hcB,lt_min heS heB,lt_min htS htB,hB,?_⟩
  intro η α hη hηsmall hα N eps τ lam θ j q sigma l s hN heps hepslt hτ hl0 hl1 htl hσj hsupp hs
  let J := mixedBranchIndexSet sigma
  let y := deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam θ
  have hj : j∈J := by simp [J,mixedBranchIndexSet,hσj]
  have hq : q∉J := by
    have hh := nested_sector_named_nonbranch d.thetaB outer inner ho hi hio q sigma l θ hsupp
    simpa only [J,mixedBranchIndexSet,Finset.mem_filter,Finset.mem_univ,true_and] using hh
  obtain ⟨hanchor,hassignment⟩ := nested_sector_jet_support d.thetaB outer inner ho hi q sigma l hsupp
  have hlabels := sector_assignment_tsupport d.thetaB inner hi sigma hassignment
  have hbranch (i : Fin N) (hiJ : i∈J) : |sectorDisplacement d.thetaB (θ i)|≤ inner := by
    have hiσ : sigma i=2 := (Finset.mem_filter.mp hiJ).2
    apply sector_branch_label_profile hi
    simpa only [hiσ] using hlabels i
  have hcompact (i : Fin N) (hiJ : i∉J) : inner/2≤|sectorDisplacement d.thetaB (θ i)| := by
    apply sector_compact_label_profile hi (sigma i) _ (hlabels i)
    simpa only [J,mixedBranchIndexSet,Finset.mem_filter,Finset.mem_univ,true_and] using hiJ
  have hsS := hs.trans (mul_le_mul_of_nonneg_right (min_le_left cS cB) heps.le)
  have hsB := hs.trans (mul_le_mul_of_nonneg_right (min_le_right cS cB) heps.le)
  obtain ⟨hb,hcpt⟩ := hCoeff η α hη hηsmall hα N eps τ lam θ s hN heps
    (hepslt.trans_le (min_le_right _ _)) hτ hl0 hl1 (htl.trans_le (min_le_right _ _)) hsB
  have hratio := (hSlope η α hη hηsmall hα N eps τ lam θ j q s hN heps
    (hepslt.trans_le (min_le_left _ _)) hτ hl0 hl1 (htl.trans_le (min_le_left _ _))
    ((hbranch j hj).trans hiS') (sectorOuterAnchor_tsupport d.thetaB outer ho q hanchor) hsS).2.1
  exact actualMixedResidualData_mem_of_bounds (by omega) J j q s y hB.le
    (hb j (hbranch j hj)).1 (hcpt q (hcompact q hq)).1
    (fun i hiJ => (hb i (hbranch i hiJ)).2) (fun i hiJ => (hcpt i (hcompact i hiJ)).2) hratio

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1500000 in
theorem mixed_actual_current_residual_data (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) :
    ∃ (inner : ℝ) (hi : 0< inner) (c e t₀ B : ℝ), 0<c ∧ 0<e ∧ 0<t₀ ∧ 0<B ∧
      ∀ η α : ℝ, 0<η → η≤ Real.sin d.thetaB/4 → 0<α → α<Real.sin d.thetaB/4 →
      ∀ (N : ℕ) (eps τ lam : ℝ) (θ : Fin N → ℝ) (j q : Fin N)
        (sigma : Fin N → Fin 3) (l : List (Fin N)) (s : ℂ),
        1≤ N → 0<eps → eps<e → 0≤τ → 0≤ lam → lam≤1 → lam*τ<t₀ → sigma j=2 →
        θ ∈ tsupport (IsingBulk.Jets.cutoffJet l (sectorAssignmentWeight d.thetaB inner hi sigma)) →
        θ ∈ tsupport (namedSelectorDerivative (constructedSelector d.thetaB η α) q) →
        ‖s-radialParameter d.theta eps‖≤ c*eps →
        actualMixedResidualData (mixedBranchIndexSet sigma) j q s
          (deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam θ)
          ∈ mixedResidualCompact B := by
  let cap := min 1 ((Real.sin d.thetaB)^2/8)
  have hcap : 0<cap := lt_min zero_lt_one (by positivity [d.a_pos])
  obtain ⟨inner,cS,eS,tS,hi,hicap,hcS,heS,htS,hSlope⟩ := mixed_actual_current_slope_separation d hcsmall cap hcap
  have hi1 : inner≤1 := hicap.trans (min_le_left _ _)
  have hieighth : inner≤(Real.sin d.thetaB)^2/8 := hicap.trans (min_le_right _ _)
  have his : inner≤(Real.sin d.thetaB)^2/4 := by nlinarith [sq_nonneg (Real.sin d.thetaB)]
  obtain ⟨cB,eB,tB,B,hcB,heB,htB,hB,hCoeff⟩ := mixed_actual_profile_coefficient_bounds d hcsmall inner hi hi1 his
  let c := min cS cB
  refine ⟨inner,hi,c,min eS eB,min tS tB,B,lt_min hcS hcB,lt_min heS heB,lt_min htS htB,hB,?_⟩
  intro η α hη hηsmall hα hαsmall N eps τ lam θ j q sigma l s hN heps hepslt hτ hl0 hl1 htl hσj hsupp hcurrent hs
  let J := mixedBranchIndexSet sigma
  let y := deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam θ
  have hj : j∈J := by simp [J,mixedBranchIndexSet,hσj]
  have hlabels := sector_assignment_cutoff_jets_support d.thetaB inner hi sigma l hsupp
  have hbranch (i : Fin N) (hiJ : i∈J) : |sectorDisplacement d.thetaB (θ i)|≤ inner := by
    have hiσ : sigma i=2 := (Finset.mem_filter.mp hiJ).2
    apply sector_branch_label_profile hi
    simpa only [hiσ] using hlabels i
  have hcompact (i : Fin N) (hiJ : i∉J) : inner/2≤|sectorDisplacement d.thetaB (θ i)| := by
    apply sector_compact_label_profile hi (sigma i) _ (hlabels i)
    simpa only [J,mixedBranchIndexSet,Finset.mem_filter,Finset.mem_univ,true_and] using hiJ
  have hq : q∉J := by
    intro hqJ
    have hqprof := hbranch q hqJ
    obtain ⟨_,_,hlo,hall,_⟩ := constructed_current_support_geometry d.thetaB η α d.a_pos hη hηsmall hα q hcurrent
    have houter := named_current_outer_profile d.a_pos hα hαsmall hlo (hall q)
    nlinarith [sq_pos_of_pos d.a_pos]
  have hsS := hs.trans (mul_le_mul_of_nonneg_right (min_le_left cS cB) heps.le)
  have hsB := hs.trans (mul_le_mul_of_nonneg_right (min_le_right cS cB) heps.le)
  obtain ⟨hb,hcpt⟩ := hCoeff η α hη hηsmall hα N eps τ lam θ s hN heps
    (hepslt.trans_le (min_le_right _ _)) hτ hl0 hl1 (htl.trans_le (min_le_right _ _)) hsB
  have hratio := (hSlope η α hη hηsmall hα hαsmall N eps τ lam θ j q s hN heps
    (hepslt.trans_le (min_le_left _ _)) hτ hl0 hl1 (htl.trans_le (min_le_left _ _))
    (hbranch j hj) hcurrent hsS).2.1
  exact actualMixedResidualData_mem_of_bounds (by omega) J j q s y hB.le
    (hb j (hbranch j hj)).1 (hcpt q (hcompact q hq)).1
    (fun i hiJ => (hb i (hbranch i hiJ)).2) (fun i hiJ => (hcpt i (hcompact i hiJ)).2) hratio


end
end IsingBulk.Tail
