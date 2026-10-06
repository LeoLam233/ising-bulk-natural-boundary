import IsingBulk.Tail.MixedActiveDataFamily
import IsingBulk.Tail.MixedActiveTransportColumn

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets Set
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The source jet constants can be selected after any sufficiently small
positive inner width. Slope separation is the actual geometric inequality. -/
theorem mixed_actual_separated_residual_jet_family (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (cap : ℝ) (hcap : 0<cap) (order : ℕ) :
    ∃ inner₀ : ℝ,0< inner₀ ∧ inner₀≤cap ∧ ∀ (inner : ℝ) (hi : 0< inner),inner≤ inner₀ →
      ∃ c e t₀ C : ℝ,0<c ∧ 0<e ∧ 0<t₀ ∧ 0<C ∧
      ∀ η α : ℝ,0<η → η≤Real.sin d.thetaB/4 → 0<α → α<Real.sin d.thetaB/4 →
      ∀ (N : ℕ) (eps τ lam : ℝ) (θ : Fin N → ℝ) (j q : Fin N)
        (sigma : Fin N → Fin 3) (l : List (Fin N)) (s : ℂ),
      1≤N → 0<eps → eps<e → 0≤τ → 0≤lam → lam≤1 → lam*τ<t₀ → θ∈angleBox N →
      sigma j=2 → sigma q≠2 →
      (θ∈tsupport (angularSelector (constructedSelector d.thetaB η α)) ∨
        θ∈tsupport (namedSelectorDerivative (constructedSelector d.thetaB η α) q)) →
      θ∈tsupport (cutoffJet l (sectorAssignmentWeight d.thetaB inner hi sigma)) →
      ‖s-radialParameter d.theta eps‖≤c*eps →
      let y := deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam θ
      let φ := fun i => mixedSourcePhase s (y i)
      let V := mixedActiveResidualData (mixedBranchIndexSet sigma) j q s φ y
      ‖mixedSourceSlope s (y q)/mixedSourceSlope s (y j)‖≤1/4 →
      JetBound (mixedResidualCore ∘ V) 0 order C ∧ JetBound (mixedCompactCore ∘ V) 0 order C := by
  let capAll := min cap ((Real.sin d.thetaB)^2/4)
  have hcapAll : 0<capAll := lt_min hcap (by positivity [d.a_pos])
  obtain ⟨inner₀,hi₀,hicap,hDataFamily⟩ := mixed_actual_active_data_jet_family d hcsmall capAll hcapAll order
  obtain ⟨cG,eG,tG,hcG,heG,htG,hGeometry⟩ := mixed_actual_uniform_source_data d hcsmall 1 zero_lt_one
  refine ⟨inner₀,hi₀,hicap.trans (min_le_left _ _),?_⟩
  intro inner hi hinner
  obtain ⟨cD,eD,tD,B,hcD,heD,htD,hB,hData⟩ := hDataFamily inner hi hinner
  obtain ⟨C,hC,hCore⟩ := mixed_residual_core_pullback_uniform_jets B order
  have his : inner≤(Real.sin d.thetaB)^2/4 := (hinner.trans hicap).trans (min_le_right _ _)
  refine ⟨min cD cG,min eD eG,min tD tG,C,lt_min hcD hcG,lt_min heD heG,lt_min htD htG,hC,?_⟩
  intro η α hη hηsmall hα hαsmall N eps τ lam θ j q sigma l s hN heps hepslt hτ hl0 hl1 htl hθ hσj hσq hSource hsupp hs
  dsimp only
  intro hsep
  let f := constructedSelector d.thetaB η α
  let y := deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ
  let φ := fun i => mixedSourcePhase s (y i)
  let J := mixedBranchIndexSet sigma
  obtain ⟨hVA,hVjets⟩ := hData η α hη hηsmall hα N eps τ lam θ j q sigma l s hN heps
    (hepslt.trans_le (min_le_left _ _)) hτ hl0 hl1 (htl.trans_le (min_le_left _ _)) hθ hσj hσq hsupp
    (hs.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) heps.le))
  have hlabel := sector_assignment_cutoff_jets_support d.thetaB inner hi sigma l hsupp j
  rw [hσj] at hlabel
  have hprofile := sector_branch_label_profile hi hlabel
  obtain ⟨_,hcoords⟩ := hGeometry η α hη hηsmall hα N eps τ lam θ s hN heps
    (hepslt.trans_le (min_le_right _ _)) hτ hl0 hl1 (htl.trans_le (min_le_right _ _))
    (hs.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) heps.le))
  obtain ⟨_,_,_,_,hW⟩ := hcoords q
  have hsin := mixed_source_branch_sine_negative d.thetaB η α inner d.a_pos hα hαsmall hi.le his θ j q hprofile hSource
  have hgap := mixed_active_data_source_gap J j q f (Real.exp_pos _) τ lam s θ hsin hW hsep
  have hne : 1-(mixedActiveResidualData J j q s φ y 0).2.1*
      (mixedActiveResidualData J j q s φ y 0).1≠0 := norm_ne_zero_iff.mp
    (ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<3/4) hgap))
  have hb := hCore (MixedActiveSpace N) (mixedActiveResidualData J j q s φ y) 0 hVA hVjets hgap
  exact ⟨⟨(mixedResidualCore_analyticAt hne).comp hVA,hC.le,fun k hk => (hb k hk).1⟩,
    ⟨(mixedCompactCore_analyticAt hne).comp hVA,hC.le,fun k hk => (hb k hk).2⟩⟩

theorem mixed_active_scaled_residual_jets {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (s : ℂ) (φ y : Fin N → ℂ) (order : ℕ) (C : ℝ)
    (hR : JetBound (mixedResidualCore ∘ mixedActiveResidualData J j q s φ y) 0 order C)
    (hQ : JetBound (mixedCompactCore ∘ mixedActiveResidualData J j q s φ y) 0 order C) :
    JetBound (mixedActiveBranchResidual J j q s φ y) 0 order ((N:ℝ)*C) ∧
    JetBound (mixedActiveCompactResidual J j q s φ y) 0 order ((N:ℝ)*C) := by
  have hR' : JetBound (fun u => (N:ℂ)*mixedResidualCore (mixedActiveResidualData J j q s φ y u)) 0 order ((N:ℝ)*C) := by
    refine ⟨analyticAt_const.mul hR.analytic,mul_nonneg (Nat.cast_nonneg N) hR.nonneg,?_⟩
    intro k hk
    exact actual_residual_dimension_scale _ _ hR.analytic N k (hR.bound k hk)
  have hQ' : JetBound (fun u => (N:ℂ)*mixedCompactCore (mixedActiveResidualData J j q s φ y u)) 0 order ((N:ℝ)*C) := by
    refine ⟨analyticAt_const.mul hQ.analytic,mul_nonneg (Nat.cast_nonneg N) hQ.nonneg,?_⟩
    intro k hk
    exact actual_residual_dimension_scale _ _ hQ.analytic N k (hQ.bound k hk)
  refine ⟨hR',?_⟩
  have he : mixedActiveCompactResidual J j q s φ y =
      fun u => -((N:ℂ)*mixedCompactCore (mixedActiveResidualData J j q s φ y u)) := by
    funext u
    simp only [mixedActiveCompactResidual,neg_mul]
  rw [he]
  exact hQ'.neg

end
end IsingBulk.Tail
