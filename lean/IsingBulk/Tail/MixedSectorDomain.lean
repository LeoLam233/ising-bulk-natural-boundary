import IsingBulk.Tail.MixedSeparatedLieStages
import IsingBulk.Tail.MixedActualResidualCoreJets
import IsingBulk.Tail.MixedBranchPairs

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem lower_halfplane_inverse_difference_ne_zero {y : ℂ} (hy : y.im<0) : y-y⁻¹≠0 := by
  have hy0 : y≠0 := by intro h; simp [h] at hy
  have hInv : 0<(y⁻¹).im := by
    rw [Complex.inv_im]
    exact div_pos (neg_pos.mpr hy) (Complex.normSq_pos.mpr hy0)
  intro he
  have hh := congrArg Complex.im (sub_eq_zero.mp he)
  linarith

/-- Shared actual-sheet and global-denominator attachment. The separation
premise is discharged by the source slope theorems in the terminal covers. -/
theorem mixed_actual_domain_from_separation (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) :
    ∃ c e t₀ : ℝ,0<c ∧ c≤1/4 ∧ 0<e ∧ 0<t₀ ∧
      ∀ η α inner : ℝ,0<η → η≤Real.sin d.thetaB/4 → 0<α → α<Real.sin d.thetaB/4 →
      0≤ inner → inner≤(Real.sin d.thetaB)^2/4 →
      ∀ (N : ℕ) (eps τ lam : ℝ) (θ : Fin N → ℝ) (J : Finset (Fin N)) (j q : Fin N) (s : ℂ),
      1≤N → 0<eps → eps<e → 0≤τ → 0≤lam → lam≤1 → lam*τ<t₀ →
      (∀ i∈J,|sectorDisplacement d.thetaB (θ i)|≤ inner) →
      (θ∈tsupport (angularSelector (constructedSelector d.thetaB η α)) ∨
        θ∈tsupport (namedSelectorDerivative (constructedSelector d.thetaB η α) q)) →
      mixedSourceSlope s (deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam θ j)-
        mixedSourceSlope s (deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam θ q)≠0 →
      ‖s-radialParameter d.theta eps‖≤c*eps →
      (s,θ)∈mixedSeparatedDomain J j q (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam := by
  obtain ⟨cG,e,t₀,hcG,he,ht,hGeometry⟩ := mixed_actual_uniform_source_data d hcsmall 1 zero_lt_one
  refine ⟨min cG (1/4),e,t₀,lt_min hcG (by norm_num),min_le_right _ _,he,ht,?_⟩
  intro η α inner hη hηsmall hα hαsmall hi his N eps τ lam θ J j q s hN heps hepslt hτ hl0 hl1 htl hBP hSource hSep hs
  let f := constructedSelector d.thetaB η α
  let r := Real.exp (-d.c₀*eps)
  have hr : 0<r := Real.exp_pos _
  have hr1 : r<1 := Real.exp_lt_one_iff.mpr (by nlinarith [d.c₀_pos])
  have hs0 : s≠0 := by
    intro heq
    have hh := hs.trans (mul_le_mul_of_nonneg_right (min_le_right cG (1/4)) heps.le)
    rw [heq,zero_sub,norm_neg,radialParameter_norm heps.le] at hh
    linarith
  obtain ⟨_,hcoords⟩ := hGeometry η α hη hηsmall hα N eps τ lam θ s hN heps hepslt hτ hl0 hl1 htl
    (hs.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) heps.le))
  refine ⟨hs0,?_,?_,hSep,?_⟩
  · intro i
    obtain ⟨_,_,_,_,hh⟩ := hcoords i
    exact hh
  · intro i hiJ
    have hsin := mixed_source_branch_sine_negative d.thetaB η α inner d.a_pos hα hαsmall hi his θ i q (hBP i hiJ) hSource
    exact lower_halfplane_inverse_difference_ne_zero (mixed_actual_deformed_lower f hr τ lam θ i hsin)
  · exact homotopy_y_gap_nonzero (by omega) f hr hr1 hτ hl0 θ
      (fun x => (thresholdStep_range _ _ _).1) (fun x => Real.smoothTransition.le_one _)


/-- Original K support is covered globally in the periodic angles. -/
theorem mixed_original_sector_domain (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (outer : ℝ) (ho : 0<outer) (cap : ℝ) (hcap : 0<cap) :
    ∃ inner₀ : ℝ,0< inner₀ ∧ inner₀≤cap ∧ ∀ (inner : ℝ) (hi : 0< inner),inner≤ inner₀ →
      ∃ c e : ℝ,0<c ∧ c≤1/4 ∧ 0<e ∧
      ∀ η α : ℝ,0<η → η≤Real.sin d.thetaB/4 → 0<α → α<Real.sin d.thetaB/4 →
      ∀ (N : ℕ) (eps τ : ℝ) (θ : Fin N → ℝ) (j q : Fin N) (sigma : Fin N → Fin 3) (s : ℂ),
      1≤N → 0<eps → eps<e → 0≤τ → sigma j=2 →
      θ∈tsupport (fun θ => angularSelector (constructedSelector d.thetaB η α) θ*
        nestedSectorWeight d.thetaB outer inner ho hi q sigma θ) →
      ‖s-radialParameter d.theta eps‖≤c*eps →
      (s,θ)∈mixedSeparatedDomain (mixedBranchIndexSet sigma) j q
        (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ 0 := by
  obtain ⟨iS,cS,eS,tS,hiS,_hiSo,hcS,heS,htS,hSlope⟩ := mixed_actual_profile_slope_separation d hcsmall outer ho
  obtain ⟨cG,eG,tG,hcG,hcGsmall,heG,htG,hDomain⟩ := mixed_actual_domain_from_separation d hcsmall
  let inner₀ := min iS (min cap ((Real.sin d.thetaB)^2/4))
  have hi₀ : 0< inner₀ := lt_min hiS (lt_min hcap (by positivity [d.a_pos]))
  refine ⟨inner₀,hi₀,(min_le_right _ _).trans (min_le_left _ _),?_⟩
  intro inner hi hinner
  have hiS' : inner≤ iS := hinner.trans (min_le_left _ _)
  have his : inner≤(Real.sin d.thetaB)^2/4 := hinner.trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨min cS cG,min eS eG,lt_min hcS hcG,(min_le_right _ _).trans hcGsmall,lt_min heS heG,?_⟩
  intro η α hη hηsmall hα hαsmall N eps τ θ j q sigma s hN heps hepslt hτ hσj hsupport hs
  have hSource := tsupport_mul_subset_left hsupport
  have hNested := tsupport_mul_subset_right hsupport
  obtain ⟨hanchor,hassign⟩ := nested_sector_jet_support d.thetaB outer inner ho hi q sigma [] hNested
  let J := mixedBranchIndexSet sigma
  have hBP (i : Fin N) (hiJ : i∈J) : |sectorDisplacement d.thetaB (θ i)|≤ inner := by
    have hσ : sigma i=2 := by simpa [J,mixedBranchIndexSet] using hiJ
    have hh := sector_assignment_tsupport d.thetaB inner hi sigma hassign i
    rw [hσ] at hh
    exact sector_branch_label_profile hi hh
  have hj : j∈J := by simp [J,mixedBranchIndexSet,hσj]
  have hSep := hSlope η α hη hηsmall hα N eps τ 0 θ j q s hN heps
    (hepslt.trans_le (min_le_left _ _)) hτ (by norm_num) (by norm_num) (by simpa using htS)
    ((hBP j hj).trans hiS') (sectorOuterAnchor_tsupport d.thetaB outer ho q hanchor)
    (hs.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) heps.le))
  exact hDomain η α inner hη hηsmall hα hαsmall hi.le his N eps τ 0 θ J j q s hN heps
    (hepslt.trans_le (min_le_right _ _)) hτ (by norm_num) (by norm_num) (by simpa using htG)
    hBP (Or.inl hSource) hSep.2.2 (hs.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) heps.le))

/-- Named-current support uses qS as the field anchor; no auxiliary outer
partition coordinate occurs in this domain cover. -/
theorem mixed_current_sector_domain (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (cap : ℝ) (hcap : 0<cap) :
    ∃ inner₀ : ℝ,0< inner₀ ∧ inner₀≤cap ∧ ∀ (inner : ℝ) (hi : 0< inner),inner≤ inner₀ →
      ∃ c e t₀ : ℝ,0<c ∧ c≤1/4 ∧ 0<e ∧ 0<t₀ ∧
      ∀ η α : ℝ,0<η → η≤Real.sin d.thetaB/4 → 0<α → α<Real.sin d.thetaB/4 →
      ∀ (N : ℕ) (eps τ lam : ℝ) (θ : Fin N → ℝ) (j qS : Fin N) (sigma : Fin N → Fin 3) (s : ℂ),
      1≤N → 0<eps → eps<e → 0≤τ → 0≤lam → lam≤1 → lam*τ<t₀ → sigma j=2 →
      θ∈tsupport (fun θ => namedSelectorDerivative (constructedSelector d.thetaB η α) qS θ*
        sectorAssignmentWeight d.thetaB inner hi sigma θ) →
      ‖s-radialParameter d.theta eps‖≤c*eps →
      (s,θ)∈mixedSeparatedDomain (mixedBranchIndexSet sigma) j qS
        (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam := by
  let capAll := min cap ((Real.sin d.thetaB)^2/4)
  have hcapAll : 0<capAll := lt_min hcap (by positivity [d.a_pos])
  obtain ⟨inner₀,cS,eS,tS,hi₀,hiCap,hcS,heS,htS,hSlope⟩ := mixed_actual_current_slope_separation d hcsmall capAll hcapAll
  obtain ⟨cG,eG,tG,hcG,hcGsmall,heG,htG,hDomain⟩ := mixed_actual_domain_from_separation d hcsmall
  refine ⟨inner₀,hi₀,hiCap.trans (min_le_left _ _),?_⟩
  intro inner hi hinner
  have his : inner≤(Real.sin d.thetaB)^2/4 := (hinner.trans hiCap).trans (min_le_right _ _)
  refine ⟨min cS cG,min eS eG,min tS tG,lt_min hcS hcG,(min_le_right _ _).trans hcGsmall,
    lt_min heS heG,lt_min htS htG,?_⟩
  intro η α hη hηsmall hα hαsmall N eps τ lam θ j qS sigma s hN heps hepslt hτ hl0 hl1 htl hσj hsupport hs
  have hSource := tsupport_mul_subset_left hsupport
  have hassign := tsupport_mul_subset_right hsupport
  let J := mixedBranchIndexSet sigma
  have hBP (i : Fin N) (hiJ : i∈J) : |sectorDisplacement d.thetaB (θ i)|≤ inner := by
    have hσ : sigma i=2 := by simpa [J,mixedBranchIndexSet] using hiJ
    have hh := sector_assignment_tsupport d.thetaB inner hi sigma hassign i
    rw [hσ] at hh
    exact sector_branch_label_profile hi hh
  have hj : j∈J := by simp [J,mixedBranchIndexSet,hσj]
  have hSep := hSlope η α hη hηsmall hα hαsmall N eps τ lam θ j qS s hN heps
    (hepslt.trans_le (min_le_left _ _)) hτ hl0 hl1 (htl.trans_le (min_le_left _ _))
    ((hBP j hj).trans hinner) hSource
    (hs.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) heps.le))
  exact hDomain η α inner hη hηsmall hα hαsmall hi.le his N eps τ lam θ J j qS s hN heps
    (hepslt.trans_le (min_le_right _ _)) hτ hl0 hl1 (htl.trans_le (min_le_right _ _))
    hBP (Or.inr hSource) hSep.2.2 (hs.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) heps.le))


/-- The auxiliary outer anchor is arbitrary and is never substituted for qS. -/
theorem named_nested_sector_support_subset {N : ℕ} (f : SelectorFunctions)
    (b outer inner : ℝ) (ho : 0<outer) (hi : 0< inner) (qS a : Fin N) (sigma : Fin N → Fin 3) :
    tsupport (fun θ => namedSelectorDerivative f qS θ*nestedSectorWeight b outer inner ho hi a sigma θ) ⊆
      tsupport (fun θ => namedSelectorDerivative f qS θ*sectorAssignmentWeight b inner hi sigma θ) := by
  have he : (fun θ => namedSelectorDerivative f qS θ*nestedSectorWeight b outer inner ho hi a sigma θ)=
      (fun θ => sectorOuterAnchor b outer ho a θ*
        (namedSelectorDerivative f qS θ*sectorAssignmentWeight b inner hi sigma θ)) := by
    funext θ
    unfold nestedSectorWeight
    ring
  rw [he]
  exact tsupport_mul_subset_right

end
end IsingBulk.Tail
