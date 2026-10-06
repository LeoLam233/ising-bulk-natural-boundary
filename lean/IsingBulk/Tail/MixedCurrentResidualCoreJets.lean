import IsingBulk.Tail.MixedActualResidualCoreJets

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem mixed_actual_current_residual_core_jets (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (cap : ℝ) (hcap : 0<cap) (order : ℕ) :
    ∃ (inner : ℝ) (hi : 0< inner) (c e t₀ C : ℝ),inner≤cap ∧ 0<c ∧ 0<e ∧ 0<t₀ ∧ 0<C ∧
      ∀ η α : ℝ,0<η → η≤Real.sin d.thetaB/4 → 0<α → α<Real.sin d.thetaB/4 →
      ∀ (N : ℕ) (eps τ lam : ℝ) (θ : Fin N → ℝ) (j q : Fin N)
        (sigma : Fin N → Fin 3) (l : List (Fin N)) (s : ℂ),
      1≤N → 0<eps → eps<e → 0≤τ → 0≤lam → lam≤1 → lam*τ<t₀ → θ∈angleBox N → sigma j=2 →
      θ∈tsupport (namedSelectorDerivative (constructedSelector d.thetaB η α) q) →
      θ∈tsupport (IsingBulk.Jets.cutoffJet l (sectorAssignmentWeight d.thetaB inner hi sigma)) →
      ‖s-radialParameter d.theta eps‖≤c*eps →
      let y := deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam θ
      let φ := fun i => mixedSourcePhase s (y i)
      let V := mixedActiveResidualData (mixedBranchIndexSet sigma) j q s φ y
      AnalyticAt ℂ (mixedResidualCore ∘ V) 0 ∧ AnalyticAt ℂ (mixedCompactCore ∘ V) 0 ∧
      ∀ k≤order,‖iteratedFDeriv ℂ k (mixedResidualCore ∘ V) 0‖≤C ∧
        ‖iteratedFDeriv ℂ k (mixedCompactCore ∘ V) 0‖≤C := by
  let capS := min cap ((Real.sin d.thetaB)^2/16)
  have hcapS : 0<capS := lt_min hcap (by positivity [d.a_pos])
  obtain ⟨iS,cS,eS,tS,hiS,hiScap,hcS,heS,htS,hSlope⟩ :=
    mixed_actual_current_slope_separation d hcsmall capS hcapS
  let capAll := iS
  have hcapAll : 0<capAll := hiS
  obtain ⟨inner,hi,cD,eD,tD,B,hicap,hcD,heD,htD,hB,hData⟩ :=
    mixed_actual_active_data_jets d hcsmall capAll hcapAll order
  obtain ⟨cG,eG,tG,hcG,heG,htG,hGeometry⟩ := mixed_actual_uniform_source_data d hcsmall 1 zero_lt_one
  obtain ⟨C,hC,hCore⟩ := mixed_residual_core_pullback_uniform_jets B order
  let c := min cD (min cS cG)
  let e := min eD (min eS eG)
  let t₀ := min tD (min tS tG)
  have hiS' : inner≤ iS := hicap
  have hi16 : inner≤(Real.sin d.thetaB)^2/16 := (hicap.trans hiScap).trans (min_le_right _ _)
  have his : inner≤(Real.sin d.thetaB)^2/4 := by nlinarith [sq_nonneg (Real.sin d.thetaB)]
  refine ⟨inner,hi,c,e,t₀,C,(hicap.trans hiScap).trans (min_le_left _ _),lt_min hcD (lt_min hcS hcG),lt_min heD (lt_min heS heG),
    lt_min htD (lt_min htS htG),hC,?_⟩
  intro η α hη hηsmall hα hαsmall N eps τ lam θ j q sigma l s hN heps hepslt hτ hl0 hl1 htl hθ hσj hSource hsupp hs
  let f := constructedSelector d.thetaB η α
  let y := deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ
  let φ := fun i => mixedSourcePhase s (y i)
  let J := mixedBranchIndexSet sigma
  have hassign := cutoffJet_tsupport_subset l _ hsupp
  have hlabels := sector_assignment_cutoff_jets_support d.thetaB inner hi sigma l hsupp
  obtain ⟨_,_,hqlo,hall,_⟩ := constructed_current_support_geometry d.thetaB η α d.a_pos hη hηsmall hα q hSource
  have hqprofile := named_current_outer_profile d.a_pos hα hαsmall hqlo (hall q)
  have hq : sigma q≠2 := by
    intro he
    have hqLabel := hlabels q
    rw [he] at hqLabel
    have hp := sector_branch_label_profile hi hqLabel
    have hsin : 0<Real.sin d.thetaB := d.a_pos
    nlinarith [sq_pos_of_pos hsin]
  have hassignJet : θ∈tsupport (IsingBulk.Jets.cutoffJet [] (sectorAssignmentWeight d.thetaB inner hi sigma)) := hassign
  obtain ⟨hVA,hVjets⟩ := hData η α hη hηsmall hα N eps τ lam θ j q sigma [] s hN heps
    (hepslt.trans_le (min_le_left _ _)) hτ hl0 hl1 (htl.trans_le (min_le_left _ _)) hθ hσj hq hassignJet
    (hs.trans (mul_le_mul_of_nonneg_right (min_le_left cD _) heps.le))
  have hlabel := sector_assignment_tsupport d.thetaB inner hi sigma hassign j
  rw [hσj] at hlabel
  have hprofile := sector_branch_label_profile hi hlabel
  have hsep := hSlope η α hη hηsmall hα hαsmall N eps τ lam θ j q s hN heps
    (hepslt.trans_le ((min_le_right eD _).trans (min_le_left eS eG))) hτ hl0 hl1
    (htl.trans_le ((min_le_right tD _).trans (min_le_left tS tG))) (hprofile.trans hiS') hSource
    (hs.trans (mul_le_mul_of_nonneg_right ((min_le_right cD _).trans (min_le_left cS cG)) heps.le))
  obtain ⟨_,hcoords⟩ := hGeometry η α hη hηsmall hα N eps τ lam θ s hN heps
    (hepslt.trans_le ((min_le_right eD _).trans (min_le_right eS eG))) hτ hl0 hl1
    (htl.trans_le ((min_le_right tD _).trans (min_le_right tS tG)))
    (hs.trans (mul_le_mul_of_nonneg_right ((min_le_right cD _).trans (min_le_right cS cG)) heps.le))
  obtain ⟨_,_,_,_,hW⟩ := hcoords q
  have hsin := mixed_source_branch_sine_negative d.thetaB η α inner d.a_pos hα hαsmall hi.le his θ j q hprofile (Or.inr hSource)
  have hgap := mixed_active_data_source_gap J j q f (Real.exp_pos _) τ lam s θ hsin hW hsep.2.1
  have hne : 1-(mixedActiveResidualData J j q s φ y 0).2.1*
      (mixedActiveResidualData J j q s φ y 0).1≠0 := norm_ne_zero_iff.mp
    (ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<3/4) hgap))
  exact ⟨(mixedResidualCore_analyticAt hne).comp hVA,
    (mixedCompactCore_analyticAt hne).comp hVA,
    hCore (MixedActiveSpace N) (mixedActiveResidualData J j q s φ y) 0 hVA hVjets hgap⟩


end
end IsingBulk.Tail
