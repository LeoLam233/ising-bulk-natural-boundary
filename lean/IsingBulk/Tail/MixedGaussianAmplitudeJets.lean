import IsingBulk.Tail.MixedActualPairFamily
import IsingBulk.Tail.MixedAmplitudeSource
import IsingBulk.Tail.MixedActualAmplitudeJets
import IsingBulk.Tail.MixedDeletedPairSource
import IsingBulk.Tail.ChangedPairProductJets

/-! Complete-pair differentiation retains the surviving Gaussian. Only the
finitely many differentiated factors pay regular scalar jet constants. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets Set
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false

def mixedActivePairProduct {N : ℕ} (J : Finset (Fin N)) (q : Fin N)
    (s : ℂ) (φ y : Fin N → ℂ) (u : MixedActiveSpace N) : ℂ :=
  ∏ p∈orderedIndexPairs (Finset.univ : Finset (Fin N)),mixedActiveCompletePair J q s φ y p.1 p.2 u

def mixedActiveRegularAmplitude {N : ℕ} (J : Finset (Fin N)) (q : Fin N)
    (s : ℂ) (φ y : Fin N → ℂ) (u : MixedActiveSpace N) : ℂ :=
  mixedActiveSmoothAmplitude J q s φ y u*mixedActivePairProduct J q s φ y u

theorem orderedIndexPairs_fin_card_le (N : ℕ) :
    (orderedIndexPairs (Finset.univ : Finset (Fin N))).card≤N^2 := by
  unfold orderedIndexPairs
  exact (Finset.card_filter_le _ _).trans_eq (by simp [pow_two])

theorem mixed_pair_product_gaussian_jets {N : ℕ} (hN : 1≤N)
    (J : Finset (Fin N)) (q : Fin N) (s : ℂ) (φ y : Fin N → ℂ)
    (order : ℕ) (C B κ : ℝ) (hC : 1≤C) (hB : 0≤B)
    (hPair : ∀ i j,AnalyticAt ℂ (mixedActiveCompletePair J q s φ y i j) 0 ∧
      ∀ k≤order,‖iteratedFDeriv ℂ k (mixedActiveCompletePair J q s φ y i j) 0‖≤C)
    (hDeleted : ∀ E : Finset (Fin N × Fin N),E.card≤order →
      (∏ p∈orderedIndexPairs (Finset.univ : Finset (Fin N)) \ E,
        ‖mixedActiveCompletePair J q s φ y p.1 p.2 0‖)≤B^N*Real.exp (-κ*(N:ℝ)^2)) :
    JetBound (mixedActivePairProduct J q s φ y) 0 order
      ((N:ℝ)^(2*order)*C^order*B^N*Real.exp (-κ*(N:ℝ)^2)) := by
  have hc : 0≤C := by linarith
  refine ⟨Finset.analyticAt_fun_prod _ (fun p _ => (hPair p.1 p.2).1),by positivity,?_⟩
  intro k hk
  have hh := analytic_product_changed_factors_bound (orderedIndexPairs (Finset.univ : Finset (Fin N)))
    (fun p => mixedActiveCompletePair J q s φ y p.1 p.2) 0 order C
    (B^N*Real.exp (-κ*(N:ℝ)^2)) hC (by positivity)
    (fun p _ => (hPair p.1 p.2).1) (fun p _ l _ hl => (hPair p.1 p.2).2 l hl)
    (fun E _ hE => hDeleted E hE) k hk
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hcard : ((orderedIndexPairs (Finset.univ : Finset (Fin N))).card:ℝ)≤(N:ℝ)^2 := by
    exact_mod_cast orderedIndexPairs_fin_card_le N
  have hpow : ((orderedIndexPairs (Finset.univ : Finset (Fin N))).card:ℝ)^k≤(N:ℝ)^(2*order) := by
    calc
      _ ≤ ((N:ℝ)^2)^k := pow_le_pow_left₀ (Nat.cast_nonneg _) hcard k
      _ = (N:ℝ)^(2*k) := (pow_mul _ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ hn (by omega)
  have hCp : C^k≤C^order := pow_le_pow_right₀ hC hk
  have hm := mul_le_mul hpow hCp (pow_nonneg hc k) (pow_nonneg (Nat.cast_nonneg N) (2*order))
  have hm2 := mul_le_mul_of_nonneg_right hm (show 0≤B^N*Real.exp (-κ*(N:ℝ)^2) by positivity)
  exact hh.trans (hm2.trans_eq (by ring))

theorem mixed_regular_amplitude_gaussian_jets {N : ℕ} (hN : 1≤N)
    (J : Finset (Fin N)) (q : Fin N) (s : ℂ) (φ y : Fin N → ℂ)
    (order : ℕ) (C A B κ : ℝ) (hC : 1≤C) (hA : 0≤A) (hB : 0≤B)
    (hPair : ∀ i j,AnalyticAt ℂ (mixedActiveCompletePair J q s φ y i j) 0 ∧
      ∀ k≤order,‖iteratedFDeriv ℂ k (mixedActiveCompletePair J q s φ y i j) 0‖≤C)
    (hDeleted : ∀ E : Finset (Fin N × Fin N),E.card≤order →
      (∏ p∈orderedIndexPairs (Finset.univ : Finset (Fin N)) \ E,
        ‖mixedActiveCompletePair J q s φ y p.1 p.2 0‖)≤B^N*Real.exp (-κ*(N:ℝ)^2))
    (hSmooth : AnalyticAt ℂ (mixedActiveSmoothAmplitude J q s φ y) 0 ∧
      ∀ k≤order,‖iteratedFDeriv ℂ k (mixedActiveSmoothAmplitude J q s φ y) 0‖≤2*A^N*(N:ℝ)^k) :
    JetBound (mixedActiveRegularAmplitude J q s φ y) 0 order
      (2^order*(2*A^N*(N:ℝ)^order)*((N:ℝ)^(2*order)*C^order*B^N*Real.exp (-κ*(N:ℝ)^2))) := by
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hs : JetBound (mixedActiveSmoothAmplitude J q s φ y) 0 order (2*A^N*(N:ℝ)^order) := by
    refine ⟨hSmooth.1,by positivity,?_⟩
    intro k hk
    exact (hSmooth.2 k hk).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hn hk) (by positivity))
  exact hs.mul (mixed_pair_product_gaussian_jets hN J q s φ y order C B κ hC hB hPair hDeleted)

theorem mixed_regular_amplitude_gaussian_jets_simplified {N : ℕ} (hN : 1≤N)
    (J : Finset (Fin N)) (q : Fin N) (s : ℂ) (φ y : Fin N → ℂ)
    (order : ℕ) (C A B κ : ℝ) (hC : 1≤C) (hA : 0≤A) (hB : 0≤B)
    (hPair : ∀ i j,AnalyticAt ℂ (mixedActiveCompletePair J q s φ y i j) 0 ∧
      ∀ k≤order,‖iteratedFDeriv ℂ k (mixedActiveCompletePair J q s φ y i j) 0‖≤C)
    (hDeleted : ∀ E : Finset (Fin N × Fin N),E.card≤order →
      (∏ p∈orderedIndexPairs (Finset.univ : Finset (Fin N)) \ E,
        ‖mixedActiveCompletePair J q s φ y p.1 p.2 0‖)≤B^N*Real.exp (-κ*(N:ℝ)^2))
    (hSmooth : AnalyticAt ℂ (mixedActiveSmoothAmplitude J q s φ y) 0 ∧
      ∀ k≤order,‖iteratedFDeriv ℂ k (mixedActiveSmoothAmplitude J q s φ y) 0‖≤2*A^N*(N:ℝ)^k) :
    JetBound (mixedActiveRegularAmplitude J q s φ y) 0 order
      ((2^(order+1)*C^order*A*B)^N*(N:ℝ)^(3*order)*Real.exp (-κ*(N:ℝ)^2)) := by
  have hh := mixed_regular_amplitude_gaussian_jets hN J q s φ y order C A B κ hC hA hB hPair hDeleted hSmooth
  apply hh.mono le_rfl
  let K : ℝ := 2^(order+1)*C^order
  have hK : 1≤K := by
    have h₁ : 1≤(2:ℝ)^(order+1) := one_le_pow₀ (by norm_num)
    have h₂ : 1≤C^order := one_le_pow₀ hC
    dsimp [K]
    nlinarith [mul_nonneg (sub_nonneg.mpr h₁) (sub_nonneg.mpr h₂)]
  have hKN : K≤K^N := by simpa only [pow_one] using pow_le_pow_right₀ hK hN
  calc
    _ = K*(A*B)^N*(N:ℝ)^(3*order)*Real.exp (-κ*(N:ℝ)^2) := by
      dsimp [K]
      simp only [mul_pow,show 2*order=order*2 by omega,show 3*order=order*3 by omega,pow_mul,pow_succ]
      ring
    _ ≤ K^N*(A*B)^N*(N:ℝ)^(3*order)*Real.exp (-κ*(N:ℝ)^2) := by gcongr
    _ = _ := by rw [mul_pow,mul_pow,mul_pow]; ring

/-- Actual current-sector regular amplitude: the Gaussian coefficient and
selector geometry precede the derivative order and particle number. -/
theorem mixed_current_regular_amplitude_jets (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) :
    ∃ η₀ : ℝ,0<η₀ ∧ ∀ η : ℝ,0<η → η<η₀ →
      ∃ α₀ τ₀ : ℝ,0<α₀ ∧ 0<τ₀ ∧ ∀ α τ : ℝ,0<α → α<α₀ → 0<τ → τ<τ₀ →
      ∃ κ : ℝ,0<κ ∧ ∀ (order : ℕ) (cap : ℝ),0<cap →
      ∃ inner₀ : ℝ,0< inner₀ ∧ inner₀≤cap ∧ ∀ (inner : ℝ) (hi : 0< inner),inner≤ inner₀ →
      ∃ c e t₀ C : ℝ,0<c ∧ 0<e ∧ 0<t₀ ∧ 0<C ∧
      ∀ (N : ℕ) (eps lam : ℝ) (θ : Fin N → ℝ) (q : Fin N)
        (sigma : Fin N → Fin 3) (l : List (Fin N)) (s : ℂ),
      1≤N → 0<eps → eps<e → 0≤lam → lam≤1 → lam*τ<t₀ → θ∈angleBox N →
      θ∈tsupport (namedSelectorDerivative (constructedSelector d.thetaB η α) q) →
      θ∈tsupport (cutoffJet l (sectorAssignmentWeight d.thetaB inner hi sigma)) →
      ‖s-radialParameter d.theta eps‖≤c*eps →
      let y := deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam θ
      let φ := fun i => mixedSourcePhase s (y i)
      JetBound (mixedActiveRegularAmplitude (mixedBranchIndexSet sigma) q s φ y) 0 order
        (C^N*(N:ℝ)^(3*order)*Real.exp (-κ*(N:ℝ)^2)) := by
  obtain ⟨ηP,hηP,hSetup⟩ := original_current_actual_source_deleted_pairs d hcsmall
  refine ⟨min ηP (Real.sin d.thetaB/4),lt_min hηP (by positivity [d.a_pos]),?_⟩
  intro η hη hηlt
  have hηsmall : η≤Real.sin d.thetaB/4 := hηlt.le.trans (min_le_right _ _)
  obtain ⟨αP,τP,hαP,hτP,hSetup⟩ := hSetup η hη (hηlt.trans_le (min_le_left _ _))
  refine ⟨min αP (Real.sin d.thetaB/4),τP,lt_min hαP (by positivity [d.a_pos]),hτP,?_⟩
  intro α τ hα hαlt hτ hτlt
  have hαsmall : α<Real.sin d.thetaB/4 := hαlt.trans_le (min_le_right _ _)
  obtain ⟨cP,eP,κ,B,hcP,heP,hB,hκ,hDeleted⟩ := hSetup α τ hα (hαlt.trans_le (min_le_left _ _)) hτ hτlt
  refine ⟨κ,hκ,?_⟩
  intro order cap hcap
  obtain ⟨iF,hiF,hiFcap,hFamily⟩ := mixed_actual_sector_pair_family d hcsmall cap hcap order
  obtain ⟨iA,hiA,hiAcap,hAmplitude⟩ := mixed_actual_smooth_amplitude_jets d hcsmall cap hcap order
  refine ⟨min iF iA,lt_min hiF hiA,(min_le_left _ _).trans hiFcap,?_⟩
  intro inner hi hinner
  obtain ⟨cF,eF,tF,CF,hcF,heF,htF,hCF,hFamily⟩ := hFamily inner hi (hinner.trans (min_le_left _ _))
  obtain ⟨cA,eA,tA,CA,hcA,heA,htA,hCA,hAmplitude⟩ := hAmplitude inner hi (hinner.trans (min_le_right _ _))
  let C := max 1 CF
  have hC : 1≤C := le_max_left _ _
  have hCp : 0<C := lt_of_lt_of_le zero_lt_one hC
  refine ⟨min cP (min cF cA),min eP (min eF eA),min tF tA,
    2^(order+1)*C^order*CA*B order,lt_min hcP (lt_min hcF hcA),lt_min heP (lt_min heF heA),
    lt_min htF htA,by positivity [hB order],?_⟩
  intro N eps lam θ q sigma l s hN heps hepslt hl0 hl1 htl hθ hSource hsupp hs
  let y := deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam θ
  let φ := fun i => mixedSourcePhase s (y i)
  let J := mixedBranchIndexSet sigma
  have hsP := hs.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) heps.le)
  have hsF := hs.trans (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) heps.le)
  have hsA := hs.trans (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) heps.le)
  have hf := hFamily η α hη hηsmall hα hαsmall N eps τ lam θ q sigma l s hN heps
    (hepslt.trans_le ((min_le_right _ _).trans (min_le_left _ _))) hτ.le hl0 hl1
    (htl.trans_le (min_le_left _ _)) hθ (Or.inr hSource) hsupp hsF
  have ha := hAmplitude η α hη hηsmall hα N eps τ lam θ q sigma l s hN heps
    (hepslt.trans_le ((min_le_right _ _).trans (min_le_right _ _))) hτ.le hl0 hl1
    (htl.trans_le (min_le_right _ _)) hθ hsupp hsA
  apply mixed_regular_amplitude_gaussian_jets_simplified hN J q s φ y order C CA (B order) κ hC hCA.le (hB order).le
  · intro i j
    exact ⟨(hf i j).2.1,fun k hk => ((hf i j).2.2 k hk).trans (le_max_right _ _)⟩
  · intro E hE
    calc
      _ = ∏ p∈orderedIndexPairs (Finset.univ : Finset (Fin N)) \ E,
          ‖canceledPair (y p.1) (y p.2) (globalRoot s (y p.1)) (globalRoot s (y p.2))‖ := by
        apply Finset.prod_congr rfl
        intro p _
        rw [(hf p.1 p.2).1]
      _ ≤ _ := hDeleted N eps lam θ q s E order hE hN heps
        (hepslt.trans_le (min_le_left _ _)) hl0 hl1 hθ hSource hsP
  · exact ha

theorem mixed_original_regular_amplitude_jets (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) :
    ∃ η₀ : ℝ,0<η₀ ∧ ∀ η : ℝ,0<η → η<η₀ →
      ∃ α₀ κ : ℝ,0<α₀ ∧ 0<κ ∧ ∀ α : ℝ,0<α → α<α₀ →
      ∀ (order : ℕ) (cap : ℝ),0<cap →
      ∃ inner₀ : ℝ,0< inner₀ ∧ inner₀≤cap ∧ ∀ (inner : ℝ) (hi : 0< inner),inner≤ inner₀ →
      ∃ c e C : ℝ,0<c ∧ 0<e ∧ 0<C ∧
      ∀ (N : ℕ) (eps : ℝ) (θ : Fin N → ℝ) (q : Fin N)
        (sigma : Fin N → Fin 3) (l : List (Fin N)) (s : ℂ),
      1≤N → 0<eps → eps<e → θ∈angleBox N →
      θ∈tsupport (angularSelector (constructedSelector d.thetaB η α)) →
      θ∈tsupport (cutoffJet l (sectorAssignmentWeight d.thetaB inner hi sigma)) →
      ‖s-radialParameter d.theta eps‖≤c*eps →
      let y := angleTuple (Real.exp (-d.c₀*eps)) θ
      let φ := fun i => mixedSourcePhase s (y i)
      JetBound (mixedActiveRegularAmplitude (mixedBranchIndexSet sigma) q s φ y) 0 order
        (C^N*(N:ℝ)^(3*order)*Real.exp (-κ*(N:ℝ)^2)) := by
  obtain ⟨ηP,hηP,hSetup⟩ := original_actual_source_deleted_pairs d hcsmall
  refine ⟨min ηP (Real.sin d.thetaB/4),lt_min hηP (by positivity [d.a_pos]),?_⟩
  intro η hη hηlt
  have hηsmall : η≤Real.sin d.thetaB/4 := hηlt.le.trans (min_le_right _ _)
  obtain ⟨αP,cP,eP,κ,B,hαP,hcP,heP,hB,hκ,hDeleted⟩ := hSetup η hη (hηlt.trans_le (min_le_left _ _))
  refine ⟨min αP (Real.sin d.thetaB/4),κ,lt_min hαP (by positivity [d.a_pos]),hκ,?_⟩
  intro α hα hαlt order cap hcap
  have hαsmall : α<Real.sin d.thetaB/4 := hαlt.trans_le (min_le_right _ _)
  obtain ⟨iF,hiF,hiFcap,hFamily⟩ := mixed_actual_sector_pair_family d hcsmall cap hcap order
  obtain ⟨iA,hiA,hiAcap,hAmplitude⟩ := mixed_actual_smooth_amplitude_jets d hcsmall cap hcap order
  refine ⟨min iF iA,lt_min hiF hiA,(min_le_left _ _).trans hiFcap,?_⟩
  intro inner hi hinner
  obtain ⟨cF,eF,tF,CF,hcF,heF,htF,hCF,hFamily⟩ := hFamily inner hi (hinner.trans (min_le_left _ _))
  obtain ⟨cA,eA,tA,CA,hcA,heA,htA,hCA,hAmplitude⟩ := hAmplitude inner hi (hinner.trans (min_le_right _ _))
  let C := max 1 CF
  have hC : 1≤C := le_max_left _ _
  have hCp : 0<C := lt_of_lt_of_le zero_lt_one hC
  refine ⟨min cP (min cF cA),min eP (min eF eA),2^(order+1)*C^order*CA*B order,
    lt_min hcP (lt_min hcF hcA),lt_min heP (lt_min heF heA),by positivity [hB order],?_⟩
  intro N eps θ q sigma l s hN heps hepslt hθ hSource hsupp hs
  let y := angleTuple (Real.exp (-d.c₀*eps)) θ
  let φ := fun i => mixedSourcePhase s (y i)
  let J := mixedBranchIndexSet sigma
  have hsP := hs.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) heps.le)
  have hsF := hs.trans (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) heps.le)
  have hsA := hs.trans (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) heps.le)
  have hf := hFamily η α hη hηsmall hα hαsmall N eps 0 0 θ q sigma l s hN heps
    (hepslt.trans_le ((min_le_right _ _).trans (min_le_left _ _))) le_rfl le_rfl zero_le_one
    (by simpa using htF) hθ (Or.inl hSource) hsupp hsF
  have ha := hAmplitude η α hη hηsmall hα N eps 0 0 θ q sigma l s hN heps
    (hepslt.trans_le ((min_le_right _ _).trans (min_le_right _ _))) le_rfl le_rfl zero_le_one
    (by simpa using htA) hθ hsupp hsA
  simp only [deformedPoint_zero] at hf ha
  apply mixed_regular_amplitude_gaussian_jets_simplified hN J q s φ y order C CA (B order) κ hC hCA.le (hB order).le
  · intro i j
    exact ⟨(hf i j).2.1,fun k hk => ((hf i j).2.2 k hk).trans (le_max_right _ _)⟩
  · intro E hE
    calc
      _ = ∏ p∈orderedIndexPairs (Finset.univ : Finset (Fin N)) \ E,
          ‖canceledPair (y p.1) (y p.2) (globalRoot s (y p.1)) (globalRoot s (y p.2))‖ := by
        apply Finset.prod_congr rfl
        intro p _
        rw [(hf p.1 p.2).1]
      _ ≤ _ := hDeleted α hα (hαlt.trans_le (min_le_left _ _)) N eps θ s E order hN hE heps
        (hepslt.trans_le (min_le_left _ _)) hθ hSource hsP
  · exact ha

end
end IsingBulk.Tail
