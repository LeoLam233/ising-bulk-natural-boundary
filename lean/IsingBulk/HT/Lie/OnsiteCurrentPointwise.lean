import IsingBulk.HT.Lie.OnsitePointwiseBudget
import IsingBulk.HT.Lie.OnsiteGaussianAmplitude
import IsingBulk.HT.Contour.OnsiteCutoffJetBounds
import IsingBulk.Tail.SelectorJacobianBounds

/-! The literal onsite named-current descendants have an all-N Gaussian
bound on the entire fixed homotopy interval. The strength is selected after
the finite-order geometry and before the homotopy variable. -/
namespace IsingBulk.HT.Lie
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail IsingBulk.Jets IsingBulk.Lie IsingBulk.HT.Contour Set Filter
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

theorem onsite_current_real_weight_pointwise (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) :
    ∃ η₀ : ℝ,0<η₀ ∧ ∀ η : ℝ,0<η → η<η₀ →
      ∃ α₀ : ℝ,0<α₀ ∧ ∀ α : ℝ,0<α → α<α₀ →
      ∀ (order : ℕ) (cap : ℝ),0<cap →
      ∃ inner₀ : ℝ,0< inner₀ ∧ inner₀≤cap ∧ ∀ (inner : ℝ) (hi : 0< inner),inner≤ inner₀ →
      ∃ τ₀ : ℝ,0<τ₀ ∧ ∀ τ : ℝ,0<τ → τ<τ₀ →
      ∃ κ c e C : ℝ,0<κ ∧ 0<c ∧ 0<e ∧ 0<C ∧
      ∀ (n k : ℕ) (eps lam : ℝ) (θ : Fin (n+1) → ℝ) (q : Fin (n+1))
        (sigma : Fin (n+1) → Fin 3) (s : ℂ),
      k≤order → 0<eps → eps<e → 0≤lam → lam≤1 → θ∈angleBox (n+1) →
      θ∈tsupport (fun x => namedSelectorDerivative (constructedSelector d.thetaB η α) q x*
        sectorAssignmentWeight d.thetaB inner hi sigma x) →
      ‖s-radialParameter d.theta eps‖≤c*eps →
      let f := constructedSelector d.thetaB η α
      let r := Real.exp (-d.c₀*eps)
      let J := mixedBranchIndexSet sigma
      ‖((lieStep (onsiteBranchField J f r τ lam))^[k]
        (fun z x => ((namedSelectorDerivative f q x*sectorAssignmentWeight d.thetaB inner hi sigma x:ℝ):ℂ)*
          onsitePulledDensity f r τ lam z x)) s θ‖≤
        C^(n+1)*((n+1:ℕ):ℝ)^(5*order)*Real.exp (-κ*((n+1:ℕ):ℝ)^2)*
          ‖mixedHybridVolume J f r τ lam s θ‖ := by
  obtain ⟨ηP,hηP,hPairSetup⟩ := original_current_actual_source_deleted_pairs d hcsmall
  obtain ⟨cG,eG,tG,hcG,_hcGsmall,heG,htG,hDomain⟩ := onsite_actual_domain_cover d hcsmall
  refine ⟨min ηP (Real.sin d.thetaB/4),lt_min hηP (by positivity [d.a_pos]),?_⟩
  intro η hη hηlt
  have hηsmall := hηlt.le.trans (min_le_right ηP (Real.sin d.thetaB/4))
  obtain ⟨αP,τP,hαP,hτP,hPairSetup⟩ := hPairSetup η hη (hηlt.trans_le (min_le_left _ _))
  refine ⟨min αP (Real.sin d.thetaB/4),lt_min hαP (by positivity [d.a_pos]),?_⟩
  intro α hα hαlt order cap hcap
  have hαsmall := hαlt.trans_le (min_le_right αP (Real.sin d.thetaB/4))
  let f := constructedSelector d.thetaB η α
  have hf : RegularSelector f := constructedSelector_regular d.thetaB η α d.a_pos hη hηsmall hα
  let capAll := min cap (min ((Real.sin d.thetaB)^2/4) (η*Real.sin d.thetaB/4))
  have hcapAll : 0<capAll := by dsimp [capAll]; positivity [d.a_pos]
  obtain ⟨iF,hiF,hiFcap,hFamily⟩ := mixed_actual_sector_pair_family d hcsmall capAll hcapAll order
  obtain ⟨iA,hiA,hiAcap,hAmplitude⟩ := onsite_actual_smooth_amplitude_jets d hcsmall capAll hcapAll order
  obtain ⟨iV,cV,eV,tV,A,hiV,hiVcap,hcV,heV,htV,hA,hVelocity⟩ :=
    onsite_actual_velocity_jets d hcsmall capAll hcapAll order
  refine ⟨min iF (min iA iV),lt_min hiF (lt_min hiA hiV),
    (min_le_left _ _).trans (hiFcap.trans (min_le_left _ _)),?_⟩
  intro inner hi hinner
  have hiF' := hinner.trans (min_le_left iF (min iA iV))
  have hiA' := hinner.trans ((min_le_right iF (min iA iV)).trans (min_le_left iA iV))
  have hiV' := hinner.trans ((min_le_right iF (min iA iV)).trans (min_le_right iA iV))
  have hiCap := hiF'.trans hiFcap
  have his := hiCap.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hip := hiCap.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨cF,eF,tF,CF,hcF,heF,htF,hCF,hFamily⟩ := hFamily inner hi hiF'
  obtain ⟨cA,eA,tA,CA,hcA,heA,htA,hCA,hAmplitude⟩ := hAmplitude inner hi hiA'
  obtain ⟨B,hB,hCut⟩ := onsite_sector_cutoff_jet_bounds f hf d.thetaB inner hi order
  refine ⟨min τP (min tF (min tA (min tV tG))),
    lt_min hτP (lt_min htF (lt_min htA (lt_min htV htG))),?_⟩
  intro τ hτ hτlt
  have hτP' := hτlt.trans_le (min_le_left _ _)
  have hτF := hτlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hτA := hτlt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hτV := hτlt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))))
  have hτG := hτlt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))))
  obtain ⟨cP,eP,κ,BP,hcP,heP,hBP,hκ,hDeleted⟩ :=
    hPairSetup α τ hα (hαlt.trans_le (min_le_left _ _)) hτ hτP'
  obtain ⟨H,hH,hJac⟩ := constructed_selector_jacobian_bound d.thetaB η α τ d.a_pos hη hηsmall hα hτ.le
  let D := 2^(order+1)*(max 1 CF)^order*CA*BP order
  have hD : 0<D := by dsimp [D]; positivity [lt_of_lt_of_le zero_lt_one (le_max_left 1 CF),hBP order]
  let C := (2*(1+4*2^order*A))^order*B*(2^order*H)*D
  have hC : 0<C := by dsimp [C]; positivity [lt_of_lt_of_le zero_lt_one hA,lt_of_lt_of_le zero_lt_one hB]
  refine ⟨κ,min cP (min cF (min cA (min cV cG))),min eP (min eF (min eA (min eV eG))),C,
    hκ,lt_min hcP (lt_min hcF (lt_min hcA (lt_min hcV hcG))),
    lt_min heP (lt_min heF (lt_min heA (lt_min heV heG))),hC,?_⟩
  intro n k eps lam θ q sigma s hk heps hepslt hl0 hl1 hθ hsupport hs
  let N := n+1
  let J := mixedBranchIndexSet sigma
  let r := Real.exp (-d.c₀*eps)
  let y := deformedPoint f r τ lam θ
  let φ := fun i => mixedSourcePhase s (y i)
  have hN : 1≤N := by dsimp [N]; omega
  have hSource := tsupport_mul_subset_left hsupport
  have hassign := tsupport_mul_subset_right hsupport
  have hprofile (i : Fin (n+1)) (hiJ : i∈J) : |sectorDisplacement d.thetaB (θ i)|≤ inner := by
    have hσ : sigma i=2 := by simpa [J,mixedBranchIndexSet] using hiJ
    have hh := sector_assignment_tsupport d.thetaB inner hi sigma hassign i
    rw [hσ] at hh
    exact sector_branch_label_profile hi hh
  obtain ⟨hbranch,hp,hm⟩ := mixed_current_active_plateaus d.thetaB η α inner d.a_pos hη hηsmall
    hα hαsmall hi.le his hip J q θ hprofile hSource
  have hlt : lam*τ≤τ := mul_le_of_le_one_left hτ.le hl1
  have hcFP : min cP (min cF (min cA (min cV cG)))≤cF :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hcAP : min cP (min cF (min cA (min cV cG)))≤cA :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hcVP : min cP (min cF (min cA (min cV cG)))≤cV :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hcGP : min cP (min cF (min cA (min cV cG)))≤cG :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have heF' := hepslt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have heA' := hepslt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have heV' := hepslt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have heG' := hepslt.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hFamily' := hFamily η α hη hηsmall hα hαsmall N eps τ lam θ q sigma [] s hN
    heps heF' hτ.le hl0 hl1 (hlt.trans_lt hτF) hθ (Or.inr hSource) hassign
    (hs.trans (mul_le_mul_of_nonneg_right hcFP heps.le))
  have hAmplitude' := hAmplitude η α hη hηsmall hα N eps τ lam θ q sigma [] s hN
    heps heA' hτ.le hl0 hl1 (hlt.trans_lt hτA) hθ hassign
    (hs.trans (mul_le_mul_of_nonneg_right hcAP heps.le))
  have hV := hVelocity η α hη hηsmall hα inner hi hiV' N eps τ lam θ sigma [] s hN
    heps heV' hτ.le hl0 hl1 (hlt.trans_lt hτV) hassign
    (hs.trans (mul_le_mul_of_nonneg_right hcVP heps.le))
  have hΩ := hDomain η α inner hη hηsmall hα hαsmall hi.le his N eps τ lam θ J q s hN
    heps heG' hτ.le hl0 hl1 (hlt.trans_lt hτG) hprofile (Or.inr hSource)
    (hs.trans (mul_le_mul_of_nonneg_right hcGP heps.le))
  have hF : JetBound (onsiteActiveRegularAmplitude J q s φ y) 0 order
      (D^N*(N:ℝ)^(3*order)*Real.exp (-κ*(N:ℝ)^2)) := by
    apply onsite_regular_amplitude_gaussian_jets_simplified hN J q s φ y order (max 1 CF)
      CA (BP order) κ (le_max_left _ _) hCA.le (hBP order).le
    · intro i j
      exact ⟨(hFamily' i j).2.1,fun l hl => ((hFamily' i j).2.2 l hl).trans (le_max_right _ _)⟩
    · intro E hE
      calc
        _ = ∏ p∈orderedIndexPairs (Finset.univ : Finset (Fin N)) \ E,
            ‖canceledPair (y p.1) (y p.2) (globalRoot s (y p.1)) (globalRoot s (y p.2))‖ := by
          apply Finset.prod_congr rfl
          intro p _
          rw [(hFamily' p.1 p.2).1]
        _ ≤ _ := hDeleted N eps lam θ q s E order hE hN heps
          (hepslt.trans_le (min_le_left _ _)) hl0 hl1 hθ hSource
          (hs.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) heps.le))
    · exact hAmplitude'
  exact onsite_actual_density_gaussian_bound J q f (Real.exp_pos _) τ lam s θ hf hΩ hbranch
    (fun i hiJ => hp i (Finset.mem_insert_of_mem hiJ))
    (fun i hiJ => hm i (Finset.mem_insert_of_mem hiJ)) _
    ((namedSelectorDerivative_smooth f hf q).mul (sector_assignment_smooth d.thetaB inner hi sigma))
    order k hk A B H D κ hA (zero_le_one.trans hB) hH.le hD.le hV hF
    (mixedDensityNormalization_norm_le f τ lam θ hH.le (hJac N (by omega) lam hl0 hl1 θ))
    (fun l hl => by simpa only [Real.norm_eq_abs] using (hCut N sigma l (hl.trans hk) θ).2 q)

end
end IsingBulk.HT.Lie
