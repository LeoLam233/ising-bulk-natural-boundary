import IsingBulk.HT.Lie.OnsitePointwiseBudget
import IsingBulk.HT.Lie.OnsiteGaussianAmplitude
import IsingBulk.HT.Contour.OnsiteCutoffJetBounds

/-! Actual onsite K descendants. The undeformed source has determinant one,
and branch transport retains every complete pair in the Gaussian estimate. -/
namespace IsingBulk.HT.Lie
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail IsingBulk.Jets IsingBulk.Lie IsingBulk.HT.Contour Set Filter
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem onsite_original_real_weight_pointwise (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) :
    ∃ η₀ : ℝ,0<η₀ ∧ ∀ η : ℝ,0<η → η<η₀ →
      ∃ α₀ κ : ℝ,0<α₀ ∧ 0<κ ∧ ∀ α : ℝ,0<α → α<α₀ →
      ∀ (order : ℕ) (cap : ℝ),0<cap →
      ∃ inner₀ : ℝ,0< inner₀ ∧ inner₀≤cap ∧ ∀ (inner : ℝ) (hi : 0< inner),inner≤ inner₀ →
      ∃ c e C : ℝ,0<c ∧ 0<e ∧ 0<C ∧
      ∀ (n k : ℕ) (eps τ : ℝ) (θ : Fin (n+1) → ℝ) (_q : Fin (n+1))
        (sigma : Fin (n+1) → Fin 3) (s : ℂ),
      k≤order → 0<eps → eps<e → 0≤τ → θ∈angleBox (n+1) →
      θ∈tsupport (fun x => angularSelector (constructedSelector d.thetaB η α) x*
        sectorAssignmentWeight d.thetaB inner hi sigma x) →
      ‖s-radialParameter d.theta eps‖≤c*eps →
      let f := constructedSelector d.thetaB η α
      let r := Real.exp (-d.c₀*eps)
      let J := mixedBranchIndexSet sigma
      ‖((lieStep (onsiteBranchField J f r τ 0))^[k]
        (fun z x => ((angularSelector f x*sectorAssignmentWeight d.thetaB inner hi sigma x:ℝ):ℂ)*
          onsitePulledDensity f r τ 0 z x)) s θ‖≤
        C^(n+1)*((n+1:ℕ):ℝ)^(5*order)*Real.exp (-κ*((n+1:ℕ):ℝ)^2)*
          ‖mixedHybridVolume J f r τ 0 s θ‖ := by
  obtain ⟨ηA,hηA,hSetup⟩ := onsite_original_regular_amplitude_jets d hcsmall
  obtain ⟨cG,eG,tG,hcG,_hcGsmall,heG,htG,hDomain⟩ := onsite_actual_domain_cover d hcsmall
  refine ⟨min ηA (Real.sin d.thetaB/4),lt_min hηA (by positivity [d.a_pos]),?_⟩
  intro η hη hηlt
  have hηsmall := hηlt.le.trans (min_le_right ηA (Real.sin d.thetaB/4))
  obtain ⟨αA,κ,hαA,hκ,hSetup⟩ := hSetup η hη (hηlt.trans_le (min_le_left _ _))
  refine ⟨min αA (Real.sin d.thetaB/4),κ,lt_min hαA (by positivity [d.a_pos]),hκ,?_⟩
  intro α hα hαlt order cap hcap
  have hαsmall := hαlt.trans_le (min_le_right αA (Real.sin d.thetaB/4))
  let f := constructedSelector d.thetaB η α
  have hf : RegularSelector f := constructedSelector_regular d.thetaB η α d.a_pos hη hηsmall hα
  let capAll := min cap (min ((Real.sin d.thetaB)^2/4) (η*Real.sin d.thetaB/4))
  have hcapAll : 0<capAll := by dsimp [capAll]; positivity [d.a_pos]
  obtain ⟨iF,hiF,hiFcap,hAmplitude⟩ := hSetup α hα (hαlt.trans_le (min_le_left _ _)) order capAll hcapAll
  obtain ⟨iV,cV,eV,tV,A,hiV,hiVcap,hcV,heV,htV,hA,hVelocity⟩ :=
    onsite_actual_velocity_jets d hcsmall capAll hcapAll order
  refine ⟨min iF iV,lt_min hiF hiV,(min_le_left _ _).trans (hiFcap.trans (min_le_left _ _)),?_⟩
  intro inner hi hinner
  have hiF' := hinner.trans (min_le_left iF iV)
  have hiV' := hinner.trans (min_le_right iF iV)
  have hiCap := hiF'.trans hiFcap
  have his := hiCap.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hip := hiCap.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨cF,eF,D,hcF,heF,hD,hAmplitude⟩ := hAmplitude inner hi hiF'
  obtain ⟨B,hB,hCut⟩ := onsite_sector_cutoff_jet_bounds f hf d.thetaB inner hi order
  let C := (2*(1+4*2^order*A))^order*B*(2^order*1)*D
  have hC : 0<C := by dsimp [C]; positivity [lt_of_lt_of_le zero_lt_one hA,lt_of_lt_of_le zero_lt_one hB]
  refine ⟨min cF (min cV cG),min eF (min eV eG),C,
    lt_min hcF (lt_min hcV hcG),lt_min heF (lt_min heV heG),hC,?_⟩
  intro n k eps τ θ q sigma s hk heps hepslt hτ hθ hsupport hs
  let N := n+1
  let J := mixedBranchIndexSet sigma
  let r := Real.exp (-d.c₀*eps)
  have hN : 1≤N := by dsimp [N]; omega
  have hSource := tsupport_mul_subset_left hsupport
  have hassign := tsupport_mul_subset_right hsupport
  have hprofile (i : Fin (n+1)) (hiJ : i∈J) : |sectorDisplacement d.thetaB (θ i)|≤ inner := by
    have hσ : sigma i=2 := by simpa [J,mixedBranchIndexSet] using hiJ
    have hh := sector_assignment_tsupport d.thetaB inner hi sigma hassign i
    rw [hσ] at hh
    exact sector_branch_label_profile hi hh
  have hbranch (i : Fin (n+1)) (hiJ : i∈J) : Real.sin (θ i)<0 :=
    mixed_source_branch_sine_negative d.thetaB η α inner d.a_pos hα hαsmall hi.le his θ i q
      (hprofile i hiJ) (Or.inl hSource)
  have hplateau (i : Fin (n+1)) (hiJ : i∈J) :
      f.p =ᶠ[𝓝 (θ i)] (fun _ => f.p (θ i)) ∧ f.m =ᶠ[𝓝 (θ i)] (fun _ => f.m (θ i)) := by
    have hc := sector_negative_lowerChord_small d.a_pos hη hi.le hip (hbranch i hiJ) (hprofile i hiJ)
    obtain ⟨hp,hm⟩ := constructed_branch_plateau_germ d.a_pos hη hηsmall hα hc
    exact ⟨hp.trans (Eventually.of_forall (fun _ => hp.eq_of_nhds.symm)),
      hm.trans (Eventually.of_forall (fun _ => hm.eq_of_nhds.symm))⟩
  have hF := hAmplitude N eps θ q sigma [] s hN heps
    (hepslt.trans_le (min_le_left _ _)) hθ hSource hassign
    (hs.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) heps.le))
  have hV := hVelocity η α hη hηsmall hα inner hi hiV' N eps τ 0 θ sigma [] s hN heps
    (hepslt.trans_le ((min_le_right _ _).trans (min_le_left _ _))) hτ le_rfl zero_le_one
    (by simpa using htV) hassign
    (hs.trans (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) heps.le))
  have hΩ := hDomain η α inner hη hηsmall hα hαsmall hi.le his N eps τ 0 θ J q s hN heps
    (hepslt.trans_le ((min_le_right _ _).trans (min_le_right _ _))) hτ le_rfl zero_le_one
    (by simpa using htG) hprofile (Or.inl hSource)
    (hs.trans (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) heps.le))
  have hnorm : ‖mixedDensityNormalization f τ 0 θ‖≤(1:ℝ)^N := by
    apply mixedDensityNormalization_norm_le _ _ _ _ zero_le_one
    simp [angularJacobian_zero]
  apply onsite_actual_density_gaussian_bound J q f (Real.exp_pos _) τ 0 s θ hf hΩ hbranch
    (fun i hiJ => (hplateau i hiJ).1) (fun i hiJ => (hplateau i hiJ).2) _
    ((angularSelector_contDiff f hf).mul (sector_assignment_smooth d.thetaB inner hi sigma))
    order k hk A B 1 D κ hA (zero_le_one.trans hB) zero_le_one hD.le hV _ hnorm
    (fun l hl => by simpa only [Real.norm_eq_abs] using (hCut N sigma l (hl.trans hk) θ).1)
  simpa only [mixedContourPhase,deformedPoint_zero] using hF

end
end IsingBulk.HT.Lie
