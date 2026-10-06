import IsingBulk.Tail.MixedSourceJetFamily
import IsingBulk.Tail.MixedSourcePlateaus
import IsingBulk.Tail.MixedActualDensityBound
import IsingBulk.Tail.MixedSectorWeights
import IsingBulk.Tail.SectorCutoffJetBounds
import IsingBulk.Tail.SelectorJacobianBounds

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets Set Filter
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

/-- Actual current-sector pointwise estimate. All scalar jets, the contour
determinant, and the real cutoff jets are internally bounded. Only the two
simple kernels and branch volume remain for absolute integration. -/
theorem mixed_current_real_weight_pointwise (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) :
    ∃ η₀ : ℝ,0<η₀ ∧ ∀ η : ℝ,0<η → η<η₀ →
      ∃ α₀ τ₀ : ℝ,0<α₀ ∧ 0<τ₀ ∧ ∀ α τ : ℝ,0<α → α<α₀ → 0<τ → τ<τ₀ →
      ∃ κ : ℝ,0<κ ∧ ∀ (order : ℕ) (outer cap : ℝ) (ho : 0<outer),0<cap →
      ∃ inner₀ : ℝ,0< inner₀ ∧ inner₀≤cap ∧ ∀ (inner : ℝ) (hi : 0< inner),inner≤ inner₀ →
      ∃ c e t₀ C : ℝ,0<c ∧ 0<e ∧ 0<t₀ ∧ 0<C ∧
      ∀ (n k : ℕ) (eps lam : ℝ) (θ : Fin (n+1) → ℝ) (j q a : Fin (n+1))
        (sigma : Fin (n+1) → Fin 3) (s : ℂ),
      k≤order → 0<eps → eps<e → 0≤lam → lam≤1 → lam*τ<t₀ → θ∈angleBox (n+1) → sigma j=2 →
      θ∈tsupport (fun x => namedSelectorDerivative (constructedSelector d.thetaB η α) q x*
        nestedSectorWeight d.thetaB outer inner ho hi a sigma x) →
      ‖s-radialParameter d.theta eps‖≤c*eps →
      let f := constructedSelector d.thetaB η α
      let r := Real.exp (-d.c₀*eps)
      let J := mixedBranchIndexSet sigma
      ‖((IsingBulk.Lie.lieStep (mixedContourVelocity J j q f r τ lam))^[k]
        (fun z x => ((namedSelectorDerivative f q x*nestedSectorWeight d.thetaB outer inner ho hi a sigma x:ℝ):ℂ)*
          pulledDensity f r τ lam z x)) s θ‖ ≤
      C^(n+1)*((n+1:ℕ):ℝ)^(5*order)*Real.exp (-κ*((n+1:ℕ):ℝ)^2)*
        (‖mixedSimpleKernel f r τ lam s θ‖*‖mixedHybridVolume J f r τ lam s θ‖) := by
  obtain ⟨ηJ,hηJ,hSetup⟩ := mixed_current_source_jet_family d hcsmall
  obtain ⟨cG,eG,tG,hcG,_hcGsmall,heG,htG,hDomain⟩ := mixed_actual_domain_from_separation d hcsmall
  refine ⟨min ηJ (Real.sin d.thetaB/4),lt_min hηJ (by positivity [d.a_pos]),?_⟩
  intro η hη hηlt
  have hηsmall := hηlt.le.trans (min_le_right ηJ (Real.sin d.thetaB/4))
  obtain ⟨αJ,τ₀,hαJ,hτ₀,hSetup⟩ := hSetup η hη (hηlt.trans_le (min_le_left _ _))
  refine ⟨min αJ (Real.sin d.thetaB/4),τ₀,lt_min hαJ (by positivity [d.a_pos]),hτ₀,?_⟩
  intro α τ hα hαlt hτ hτlt
  have hαsmall := hαlt.trans_le (min_le_right αJ (Real.sin d.thetaB/4))
  obtain ⟨κ,hκ,hJets⟩ := hSetup α τ hα (hαlt.trans_le (min_le_left _ _)) hτ hτlt
  let f := constructedSelector d.thetaB η α
  have hf : RegularSelector f := constructedSelector_regular d.thetaB η α d.a_pos hη hηsmall hα
  obtain ⟨H,hH,hJac⟩ := constructed_selector_jacobian_bound d.thetaB η α τ d.a_pos hη hηsmall hα hτ.le
  refine ⟨κ,hκ,?_⟩
  intro order outer cap ho hcap
  let capAll := min cap (min ((Real.sin d.thetaB)^2/4) (η*Real.sin d.thetaB/4))
  have hcapAll : 0<capAll := by dsimp [capAll]; positivity [d.a_pos]
  obtain ⟨iJ,hiJ,_hiJcap,hJets⟩ := hJets order capAll hcapAll
  obtain ⟨iS,cS,eS,tS,hiS,hiScap,hcS,heS,htS,hSlope⟩ :=
    mixed_actual_current_slope_separation d hcsmall capAll hcapAll
  refine ⟨min iJ iS,lt_min hiJ hiS,(min_le_right _ _).trans (hiScap.trans (min_le_left _ _)),?_⟩
  intro inner hi hinner
  have hinnerCap : inner≤capAll := (hinner.trans (min_le_right _ _)).trans hiScap
  have his : inner≤(Real.sin d.thetaB)^2/4 := hinnerCap.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hip : inner≤η*Real.sin d.thetaB/4 := hinnerCap.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨cJ,eJ,tJ,A,D,hcJ,heJ,htJ,hA,hD,hJets⟩ := hJets inner hi (hinner.trans (min_le_left _ _))
  obtain ⟨B,hB,hCut⟩ := nested_sector_cutoff_jet_bounds f hf d.thetaB outer inner ho hi order
  let C := (2*(1+4*2^order*A))^order*B*H*D
  have hC : 0<C := by dsimp [C]; positivity [lt_of_lt_of_le zero_lt_one hA,lt_of_lt_of_le zero_lt_one hB]
  refine ⟨min cJ (min cS cG),min eJ (min eS eG),min tJ (min tS tG),C,
    lt_min hcJ (lt_min hcS hcG),lt_min heJ (lt_min heS heG),lt_min htJ (lt_min htS htG),hC,?_⟩
  intro n k eps lam θ j q a sigma s hk heps hepslt hl0 hl1 htl hθ hσj hsupport hs
  let J := mixedBranchIndexSet sigma
  have hSource := tsupport_mul_subset_left hsupport
  have hNested := tsupport_mul_subset_right hsupport
  obtain ⟨_,hassign⟩ := nested_sector_jet_support d.thetaB outer inner ho hi a sigma [] hNested
  have hprofile (i : Fin (n+1)) (hiJ : i∈J) : |sectorDisplacement d.thetaB (θ i)|≤ inner := by
    have hσ : sigma i=2 := by simpa [J,mixedBranchIndexSet] using hiJ
    have hh := sector_assignment_tsupport d.thetaB inner hi sigma hassign i
    rw [hσ] at hh
    exact sector_branch_label_profile hi hh
  have hj : j∈J := by simp [J,mixedBranchIndexSet,hσj]
  obtain ⟨hbranch,hp,hm⟩ := mixed_current_active_plateaus d.thetaB η α inner d.a_pos hη hηsmall
    hα hαsmall hi.le his hip J q θ hprofile hSource
  have hq : q∉J := by
    intro hq
    have hsin := hbranch q hq
    have hsq := (constructed_current_support_geometry d.thetaB η α d.a_pos hη hηsmall hα q hSource).2.2.1
    linarith
  have hσq : sigma q≠2 := by simpa [J,mixedBranchIndexSet] using hq
  have hsJ := hs.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) heps.le)
  have hsS := hs.trans (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) heps.le)
  have hsG := hs.trans (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) heps.le)
  have hsep := hSlope η α hη hηsmall hα hαsmall (n+1) eps τ lam θ j q s (by omega) heps
    (hepslt.trans_le ((min_le_right _ _).trans (min_le_left _ _))) hτ.le hl0 hl1
    (htl.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    ((hprofile j hj).trans (hinner.trans (min_le_right _ _))) hSource hsS
  obtain ⟨hR,hQ,hV,hF⟩ := hJets (n+1) eps lam θ j q sigma [] s (by omega) heps
    (hepslt.trans_le (min_le_left _ _)) hl0 hl1 (htl.trans_le (min_le_left _ _)) hθ hσj hσq hSource hassign hsJ hsep.2.1
  have hΩ := hDomain η α inner hη hηsmall hα hαsmall hi.le his (n+1) eps τ lam θ J j q s (by omega) heps
    (hepslt.trans_le ((min_le_right _ _).trans (min_le_right _ _))) hτ.le hl0 hl1
    (htl.trans_le ((min_le_right _ _).trans (min_le_right _ _))) hprofile (Or.inr hSource) hsep.2.2 hsG
  have hnorm := mixedDensityNormalization_norm_le f τ lam θ hH.le (hJac (n+1) (by omega) lam hl0 hl1 θ)
  exact mixed_actual_density_gaussian_bound J j q hj hq f (Real.exp_pos _) τ lam s θ hf.p_smooth hf.m_smooth
    hΩ hbranch hp hm order k hk A B H D κ hA (zero_le_one.trans hB) hH.le hD.le hR hQ hV hF hnorm _
    ((namedSelectorDerivative_smooth f hf q).mul (nestedSectorWeight_smooth d.thetaB outer inner ho hi a sigma))
    (fun l hl => by simpa only [Real.norm_eq_abs] using (hCut (n+1) a sigma l (hl.trans hk) θ).2.2 q)

end
end IsingBulk.Tail
