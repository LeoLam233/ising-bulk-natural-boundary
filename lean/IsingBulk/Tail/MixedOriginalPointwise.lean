import IsingBulk.Tail.MixedCurrentPointwise

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets Set Filter
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

/-- Actual original mixed-sector estimate. At lambda zero the contour and
field are selector-independent; thus no plateau is imposed on the original
outer anchor. Every real cutoff derivative is included. -/
theorem mixed_original_weight_pointwise (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) :
    ∃ η₀ : ℝ,0<η₀ ∧ ∀ η : ℝ,0<η → η<η₀ →
      ∃ α₀ κ : ℝ,0<α₀ ∧ 0<κ ∧ ∀ α : ℝ,0<α → α<α₀ →
      ∀ (order : ℕ) (outer cap : ℝ) (ho : 0<outer),0<cap →
      ∃ inner₀ : ℝ,0< inner₀ ∧ inner₀≤cap ∧ ∀ (inner : ℝ) (hi : 0< inner),inner≤ inner₀ →
      ∃ c e C : ℝ,0<c ∧ 0<e ∧ 0<C ∧
      ∀ (n k : ℕ) (eps τ : ℝ) (θ : Fin (n+1) → ℝ) (j q : Fin (n+1))
        (sigma : Fin (n+1) → Fin 3) (s : ℂ),
      k≤order → 0<eps → eps<e → 0≤τ → θ∈angleBox (n+1) → sigma j=2 →
      θ∈tsupport (fun x => angularSelector (constructedSelector d.thetaB η α) x*
        nestedSectorWeight d.thetaB outer inner ho hi q sigma x) →
      ‖s-radialParameter d.theta eps‖≤c*eps →
      let f := constructedSelector d.thetaB η α
      let r := Real.exp (-d.c₀*eps)
      let J := mixedBranchIndexSet sigma
      ‖((IsingBulk.Lie.lieStep (mixedContourVelocity J j q f r τ 0))^[k]
        (fun z x => originalMixedWeight f d.thetaB outer inner ho hi q sigma x*pulledDensity f r τ 0 z x)) s θ‖ ≤
      C^(n+1)*((n+1:ℕ):ℝ)^(5*order)*Real.exp (-κ*((n+1:ℕ):ℝ)^2)*
        (‖mixedSimpleKernel f r τ 0 s θ‖*‖mixedHybridVolume J f r τ 0 s θ‖) := by
  obtain ⟨ηJ,hηJ,hSetup⟩ := mixed_original_source_jet_family d hcsmall
  obtain ⟨cG,eG,tG,hcG,_hcGsmall,heG,htG,hDomain⟩ := mixed_actual_domain_from_separation d hcsmall
  refine ⟨min ηJ (Real.sin d.thetaB/4),lt_min hηJ (by positivity [d.a_pos]),?_⟩
  intro η hη hηlt
  have hηsmall := hηlt.le.trans (min_le_right ηJ (Real.sin d.thetaB/4))
  obtain ⟨αJ,κ,hαJ,hκ,hJets⟩ := hSetup η hη (hηlt.trans_le (min_le_left _ _))
  refine ⟨min αJ (Real.sin d.thetaB/4),κ,lt_min hαJ (by positivity [d.a_pos]),hκ,?_⟩
  intro α hα hαlt order outer cap ho hcap
  have hαsmall := hαlt.trans_le (min_le_right αJ (Real.sin d.thetaB/4))
  let f := constructedSelector d.thetaB η α
  have hf : RegularSelector f := constructedSelector_regular d.thetaB η α d.a_pos hη hηsmall hα
  let capAll := min cap ((Real.sin d.thetaB)^2/4)
  have hcapAll : 0<capAll := by dsimp [capAll]; positivity [d.a_pos]
  obtain ⟨iJ,hiJ,hiJcap,hJets⟩ := hJets α hα (hαlt.trans_le (min_le_left _ _)) order capAll hcapAll
  obtain ⟨iS,cS,eS,tS,hiS,hiSo,hcS,heS,htS,hSlope⟩ :=
    mixed_actual_profile_slope_separation d hcsmall outer ho
  refine ⟨min iJ iS,lt_min hiJ hiS,(min_le_left _ _).trans (hiJcap.trans (min_le_left _ _)),?_⟩
  intro inner hi hinner
  have hinnerCap : inner≤capAll := (hinner.trans (min_le_left _ _)).trans hiJcap
  have his : inner≤(Real.sin d.thetaB)^2/4 := hinnerCap.trans (min_le_right _ _)
  have hio : inner≤outer/4 := (hinner.trans (min_le_right _ _)).trans hiSo
  obtain ⟨cJ,eJ,A,D,hcJ,heJ,hA,hD,hJets⟩ := hJets inner hi (hinner.trans (min_le_left _ _))
  obtain ⟨B,hB,hCut⟩ := nested_sector_cutoff_jet_bounds f hf d.thetaB outer inner ho hi order
  let C := (2*(1+4*2^order*A))^order*B*1*D
  have hC : 0<C := by dsimp [C]; positivity [lt_of_lt_of_le zero_lt_one hA,lt_of_lt_of_le zero_lt_one hB]
  refine ⟨min cJ (min cS cG),min eJ (min eS eG),C,
    lt_min hcJ (lt_min hcS hcG),lt_min heJ (lt_min heS heG),hC,?_⟩
  intro n k eps τ θ j q sigma s hk heps hepslt hτ hθ hσj hsupport hs
  let J := mixedBranchIndexSet sigma
  let r := Real.exp (-d.c₀*eps)
  let w := fun x => angularSelector f x*nestedSectorWeight d.thetaB outer inner ho hi q sigma x
  have hSource := tsupport_mul_subset_left hsupport
  have hNested := tsupport_mul_subset_right hsupport
  obtain ⟨hanchor,hassign⟩ := nested_sector_jet_support d.thetaB outer inner ho hi q sigma [] hNested
  have hprofile (i : Fin (n+1)) (hiJ : i∈J) : |sectorDisplacement d.thetaB (θ i)|≤ inner := by
    have hσ : sigma i=2 := by simpa [J,mixedBranchIndexSet] using hiJ
    have hh := sector_assignment_tsupport d.thetaB inner hi sigma hassign i
    rw [hσ] at hh
    exact sector_branch_label_profile hi hh
  have hj : j∈J := by simp [J,mixedBranchIndexSet,hσj]
  have hσq := nested_sector_named_nonbranch d.thetaB outer inner ho hi hio q sigma [] θ hNested
  have hq : q∉J := by simpa [J,mixedBranchIndexSet] using hσq
  have hbranch (i : Fin (n+1)) (hiJ : i∈J) : Real.sin (θ i)<0 :=
    mixed_source_branch_sine_negative d.thetaB η α inner d.a_pos hα hαsmall hi.le his θ i q
      (hprofile i hiJ) (Or.inl hSource)
  have hsJ := hs.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) heps.le)
  have hsS := hs.trans (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) heps.le)
  have hsG := hs.trans (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) heps.le)
  have hsep := hSlope η α hη hηsmall hα (n+1) eps τ 0 θ j q s (by omega) heps
    (hepslt.trans_le ((min_le_right _ _).trans (min_le_left _ _))) hτ le_rfl zero_le_one (by simpa using htS)
    ((hprofile j hj).trans (hinner.trans (min_le_right _ _)))
    (sectorOuterAnchor_tsupport d.thetaB outer ho q hanchor) hsS
  obtain ⟨hR,hQ,hV,hF⟩ := hJets (n+1) eps θ j q sigma [] s (by omega) heps
    (hepslt.trans_le (min_le_left _ _)) hθ hσj hσq hSource hassign hsJ (by simpa only [deformedPoint_zero] using hsep.2.1)
  have hΩ := hDomain η α inner hη hηsmall hα hαsmall hi.le his (n+1) eps τ 0 θ J j q s (by omega) heps
    (hepslt.trans_le ((min_le_right _ _).trans (min_le_right _ _))) hτ le_rfl zero_le_one (by simpa using htG)
    hprofile (Or.inl hSource) hsep.2.2 hsG
  have hΩ₀ : (s,θ)∈mixedSeparatedDomain J j q mixedZeroSelector r τ 0 := by
    simpa only [mixedSeparatedDomain,mem_ofPred_eq,deformedPoint_zero] using hΩ
  have hnorm : ‖mixedDensityNormalization mixedZeroSelector τ 0 θ‖≤(1:ℝ)^(n+1) := by
    apply mixedDensityNormalization_norm_le _ _ _ _ zero_le_one
    simp [angularJacobian_zero,Matrix.det_diagonal,norm_pow]
  have hh := mixed_actual_density_gaussian_bound J j q hj hq mixedZeroSelector (Real.exp_pos _) τ 0 s θ
    contDiff_const contDiff_const hΩ₀ hbranch
    (fun _ _ => Eventually.of_forall (fun _ => rfl)) (fun _ _ => Eventually.of_forall (fun _ => rfl))
    order k hk A B 1 D κ hA (zero_le_one.trans hB) zero_le_one hD.le
    (by simpa only [mixedContourPhase,deformedPoint_zero] using hR)
    (by simpa only [mixedContourPhase,deformedPoint_zero] using hQ)
    (by simpa only [mixedContourPhase,deformedPoint_zero] using hV)
    (by simpa only [mixedContourPhase,deformedPoint_zero] using hF) hnorm w
    ((angularSelector_contDiff f hf).mul (nestedSectorWeight_smooth d.thetaB outer inner ho hi q sigma))
    (fun l hl => by simpa only [Real.norm_eq_abs] using (hCut (n+1) q sigma l (hl.trans hk) θ).2.1)
  have he : (fun z x => originalMixedWeight f d.thetaB outer inner ho hi q sigma x*pulledDensity f r τ 0 z x)=
      (fun z x => (w x:ℂ)*pulledDensity mixedZeroSelector r τ 0 z x) := by
    funext z x
    rw [pulledDensity_zero_independent f mixedZeroSelector]
    rfl
  dsimp only
  rw [he,mixed_velocity_zero_independent J j q f mixedZeroSelector]
  simpa only [mixedSimpleKernel,mixedHybridVolume,deformedPoint_zero] using hh

end
end IsingBulk.Tail
