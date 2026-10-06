import IsingBulk.Tail.SelectorOriginal
import IsingBulk.Tail.OriginalCompletePairProduct
import IsingBulk.Tail.OriginalCurrentCompletePair

/-! Direct source deleted-edge estimates. No complete-pair factor is divided out. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem complete_pair_deleted_chord_three_group_bound {N : ℕ} (b η : ℝ)
    (θ : Fin N → ℝ) (z y : Fin N → ℂ) (E : Finset (Fin N × Fin N)) (j : ℕ)
    (hN : 1 ≤ N) (hE : E.card ≤ j) {q σ : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (hhalf : 1/2 ≤ q) (hσ : 0 ≤ σ)
    (hslack : Real.log (1+σ) ≤ -Real.log q/4)
    (hB : ∀ i j, lowerChord b (θ i) < η^2/2 → lowerChord b (θ j) < η^2/2 →
      ‖canceledPair (y i) (y j) (z i) (z j)‖ ≤ 1/2)
    (hC : ∀ i j, η^2/2 ≤ lowerChord b (θ i) → η^2/2 ≤ lowerChord b (θ j) →
      (1 ≤ limitingAngularW b (θ i) ↔ 1 ≤ limitingAngularW b (θ j)) →
      ‖canceledPair (y i) (y j) (z i) (z j)‖ ≤ q)
    (hX : ∀ i j, η^2/2 ≤ lowerChord b (θ i) ∨ η^2/2 ≤ lowerChord b (θ j) →
      ‖canceledPair (y i) (y j) (z i) (z j)‖ ≤ 1+σ) :
    (∏ p ∈ orderedIndexPairs (Finset.univ : Finset (Fin N)) \ E,
      ‖canceledPair (y p.1) (y p.2) (z p.1) (z p.2)‖) ≤
      (Real.exp (-Real.log q*((j:ℝ)+1/2)))^N*
      Real.exp (-(-Real.log q/12)*(N:ℝ)^2) := by
  have hs : ∀ i k, completePairSourceColor b η (θ i)=completePairSourceColor b η (θ k) →
      ‖canceledPair (y i) (y k) (z i) (z k)‖ ≤ q := by
    intro i k he
    rcases completePairSourceColor_eq_cases he with hB' | hC'
    · exact (hB i k hB'.1 hB'.2).trans hhalf
    · exact hC i k hC'.1 hC'.2.1 hC'.2.2
  have hx : ∀ i k, completePairSourceColor b η (θ i)≠completePairSourceColor b η (θ k) →
      ‖canceledPair (y i) (y k) (z i) (z k)‖ ≤ 1+σ := by
    intro i k he
    exact hX i k (completePairSourceColor_ne_compact he)
  have hh := complete_pair_deleted_three_group_bound z y (fun i => completePairSourceColor b η (θ i)) E j hE hq hq1 hσ hslack hs hx
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  rw [← Real.exp_nat_mul,← Real.exp_add,← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hl : Real.log q < 0 := Real.log_neg hq hq1
  have hmul := mul_nonneg (neg_nonneg.mpr hl.le)
    (show 0 ≤ (j:ℝ)*((N:ℝ)-1) by positivity)
  nlinarith

theorem original_actual_deleted_pair_product (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η < η₀ →
      ∃ α₀ c e κ : ℝ, ∃ B : ℕ → ℝ, 0 < α₀ ∧ 0 < c ∧ 0 < e ∧ (∀ j, 0 < B j) ∧ 0 < κ ∧
      ∀ α : ℝ, 0 < α → α < α₀ → ∀ (N : ℕ) (eps : ℝ) (θ : Fin N → ℝ) (s : ℂ) (E : Finset (Fin N × Fin N)) (j : ℕ),
        1 ≤ N → E.card ≤ j →
        0 < eps → eps < e → θ ∈ angleBox N →
        θ ∈ tsupport (angularSelector (constructedSelector d.thetaB η α)) →
        ‖s-radialParameter d.theta eps‖ ≤ c*eps →
        let y := fun i => radialAnglePoint (-d.c₀*eps) (θ i)
        (∏ p ∈ orderedIndexPairs (Finset.univ : Finset (Fin N)) \ E,
          ‖canceledPair (y p.1) (y p.2) (selectedContinuedRoot s (y p.1)) (selectedContinuedRoot s (y p.2))‖) ≤
          (B j)^N*Real.exp (-κ*(N:ℝ)^2) := by
  obtain ⟨η₀,cB,eB,hη₀,hcB,heB,hB⟩ := original_actual_branch_pair_bound d hcsmall
  refine ⟨η₀,hη₀,?_⟩
  intro η hη hηlt
  obtain ⟨qC,hqC,hqC1,htransfer⟩ := protected_complete_pair_source_transfer (radialParameter d.theta 0)
    (sourceS_radial_zero_branch d) d.a_pos hη
  let q := max qC (1/2:ℝ)
  have hq : 0 < q := lt_of_lt_of_le hqC (le_max_left _ _)
  have hq1 : q < 1 := max_lt hqC1 (by norm_num)
  have hqhalf : 1/2 ≤ q := le_max_right _ _
  have hlog : Real.log q < 0 := Real.log_neg hq hq1
  let σ := Real.exp (-Real.log q/8)-1
  have hσ : 0 < σ := by dsimp [σ]; have := Real.one_lt_exp_iff.mpr (by linarith : 0 < -Real.log q/8); linarith
  have hslack : Real.log (1+σ) ≤ -Real.log q/4 := by
    have he : 1+σ=Real.exp (-Real.log q/8) := by dsimp [σ]; ring
    rw [he,Real.log_exp]
    linarith
  obtain ⟨δ,hδ,htuple⟩ := htransfer σ hσ
  obtain ⟨r,hr,_hr1,hinput⟩ := actual_original_pair_inputs d hδ
  let α₀ := min r (η^2/(24*Real.sin d.thetaB))
  let c := min cB r
  refine ⟨α₀,c,min eB (min r 1),-Real.log q/12,(fun j => Real.exp (-Real.log q*((j:ℝ)+1/2))),
    lt_min hr (by positivity [d.a_pos]),lt_min hcB hr,lt_min heB (lt_min hr zero_lt_one),
    (fun _ => Real.exp_pos _),by linarith,?_⟩
  intro α hα hαlt N eps θ s E j hN hE heps hepslt hθ hsupp hsd
  have hαr := hαlt.trans_le (min_le_left _ _)
  have hαch := hαlt.le.trans (min_le_right _ _)
  have hepsr := hepslt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have heps1 := hepslt.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hc : 0 < c := lt_min hcB hr
  have hsr : ‖s-radialParameter d.theta eps‖ ≤ r :=
    hsd.trans ((mul_le_of_le_one_right hc.le heps1).trans (min_le_right _ _))
  let y := fun i : Fin N => radialAnglePoint (-d.c₀*eps) (θ i)
  let z := fun i => selectedContinuedRoot s (y i)
  have hsine (i : Fin N) := constructed_original_support_sine_upper d.thetaB η α hα i hsupp
  have hm (i : Fin N) := hinput eps α (θ i) s heps.le hepsr hα.le hαr hsr (hsine i)
  have hp (i j : Fin N) (hcompact : η^2/2 ≤ lowerChord d.thetaB (θ i) ∨ η^2/2 ≤ lowerChord d.thetaB (θ j)) :=
    htuple α (θ i) (θ j) hα.le hαch ⟨hθ.1 i,hθ.2 i⟩ ⟨hθ.1 j,hθ.2 j⟩
      (hsine i) (hsine j) hcompact (y i) (y j) (z i) (z j)
      (by simpa only [lowerCircleProjection,y,mul_comm] using (hm i).1)
      (by simpa only [lowerCircleProjection,y,mul_comm] using (hm j).1)
      (hm i).2 (hm j).2
  apply complete_pair_deleted_chord_three_group_bound d.thetaB η θ z y E j hN hE hq hq1 hqhalf hσ.le hslack
  · intro i j hi hj
    exact hB η eps (θ i) (θ j) s hη hηlt heps (hepslt.trans_le (min_le_left _ _))
      (hθ.1 i) (hθ.2 i) (hθ.1 j) (hθ.2 j) hi hj
      (hsd.trans (mul_le_mul_of_nonneg_right (min_le_left cB r) heps.le))
  · intro i j hi hj hcol
    exact ((hp i j (Or.inl hi)).2 ⟨hi,hj,hcol⟩).trans (le_max_left _ _)
  · intro i j hcpt
    exact (hp i j hcpt).1

theorem original_current_actual_deleted_pair_product (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η < η₀ →
      ∃ α₀ τ₀ : ℝ, 0 < α₀ ∧ 0 < τ₀ ∧ ∀ α τ : ℝ,
        0 < α → α < α₀ → 0 < τ → τ < τ₀ →
        ∃ c e κ : ℝ, ∃ B : ℕ → ℝ, 0 < c ∧ 0 < e ∧ (∀ j, 0 < B j) ∧ 0 < κ ∧
        ∀ (N : ℕ) (eps lam : ℝ) (θ : Fin N → ℝ) (qidx : Fin N) (s : ℂ) (E : Finset (Fin N × Fin N)) (j : ℕ),
          E.card ≤ j →
          1 ≤ N → 0 < eps → eps < e → 0 ≤ lam → lam ≤ 1 →
          θ ∈ angleBox N → θ ∈ tsupport (namedSelectorDerivative (constructedSelector d.thetaB η α) qidx) →
          ‖s-radialParameter d.theta eps‖ ≤ c*eps →
          let y := deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam θ
          (∏ p ∈ orderedIndexPairs (Finset.univ : Finset (Fin N)) \ E,
            ‖canceledPair (y p.1) (y p.2) (selectedContinuedRoot s (y p.1)) (selectedContinuedRoot s (y p.2))‖) ≤
            (B j)^N*Real.exp (-κ*(N:ℝ)^2) := by
  obtain ⟨ηB,τB,hηB,hτB,hbranch⟩ := original_current_actual_branch_pair_bound d hcsmall
  refine ⟨min ηB (Real.sin d.thetaB/4),lt_min hηB (by positivity [d.a_pos]),?_⟩
  intro η hη hηlt
  have hηsmall := hηlt.le.trans (min_le_right _ _)
  obtain ⟨qC,hqC,hqC1,htransfer⟩ := protected_complete_pair_source_transfer (radialParameter d.theta 0)
    (sourceS_radial_zero_branch d) d.a_pos hη
  let q := max qC (1/2:ℝ)
  have hq : 0 < q := lt_of_lt_of_le hqC (le_max_left _ _)
  have hq1 : q < 1 := max_lt hqC1 (by norm_num)
  have hqhalf : 1/2 ≤ q := le_max_right _ _
  have hlog : Real.log q < 0 := Real.log_neg hq hq1
  let σ := Real.exp (-Real.log q/8)-1
  have hσ : 0 < σ := by dsimp [σ]; have := Real.one_lt_exp_iff.mpr (by linarith : 0 < -Real.log q/8); linarith
  have hslack : Real.log (1+σ) ≤ -Real.log q/4 := by
    have he : 1+σ=Real.exp (-Real.log q/8) := by dsimp [σ]; ring
    rw [he,Real.log_exp]
    linarith
  obtain ⟨δ,hδ,htuple⟩ := htransfer σ hσ
  obtain ⟨r,hr,hr1,hinput⟩ := original_current_pair_inputs d hδ
  let α₀ := min (Real.sin d.thetaB/4) (min r (η^2/(24*Real.sin d.thetaB)))
  refine ⟨α₀,min τB r,lt_min (by positivity [d.a_pos]) (lt_min hr (by positivity [d.a_pos])),
    lt_min hτB hr,?_⟩
  intro α τ hα hαlt hτ hτlt
  have hαsmall : α < Real.sin d.thetaB/4 := hαlt.trans_le (min_le_left _ _)
  have hαr : α < r := hαlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hαch : α ≤ η^2/(24*Real.sin d.thetaB) := hαlt.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨cB,eB,hcB,heB,hB⟩ := hbranch η α τ hη (hηlt.trans_le (min_le_left _ _))
    hα hαsmall hτ (hτlt.trans_le (min_le_left _ _))
  let c := min cB r
  refine ⟨c,min eB r,-Real.log q/12,(fun j => Real.exp (-Real.log q*((j:ℝ)+1/2))),lt_min hcB hr,lt_min heB hr,
    (fun _ => Real.exp_pos _),by linarith,?_⟩
  intro N eps lam θ qidx s E j hE hN heps hepslt hl0 hl1 hθ hsupp hsd
  have hc : 0<c := lt_min hcB hr
  have heps1 : eps≤1 := (hepslt.le.trans (min_le_right _ _)).trans (by linarith)
  have hrad : ‖s-radialParameter d.theta eps‖≤c :=
    hsd.trans (mul_le_of_le_one_right hc.le heps1)
  have hsB := hsd.trans (mul_le_mul_of_nonneg_right (min_le_left cB r) heps.le)
  let f := constructedSelector d.thetaB η α
  let y := deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ
  let z := fun i => selectedContinuedRoot s (y i)
  have hsine := (constructed_current_support_geometry d.thetaB η α d.a_pos hη hηsmall hα qidx hsupp).2.2.2.1
  have hm (i : Fin N) := hinput N eps τ lam α c f θ s hN heps.le
    (hepslt.trans_le (min_le_right _ _)) hτ.le (hτlt.trans_le (min_le_right _ _))
    hl0 hl1 hα.le hαr (min_le_right _ _)
    (fun x => thresholdStep_range _ _ _) (fun x => ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩)
    hrad i (hsine i)
  have hp (i j : Fin N) (hcompact : η^2/2 ≤ lowerChord d.thetaB (θ i) ∨ η^2/2 ≤ lowerChord d.thetaB (θ j)) :=
    htuple α (θ i) (θ j) hα.le hαch ⟨hθ.1 i,hθ.2 i⟩ ⟨hθ.1 j,hθ.2 j⟩
      (hsine i) (hsine j) hcompact (y i) (y j) (z i) (z j)
      (by simpa only [lowerCircleProjection,y,mul_comm] using (hm i).1)
      (by simpa only [lowerCircleProjection,y,mul_comm] using (hm j).1)
      (hm i).2 (hm j).2
  apply complete_pair_deleted_chord_three_group_bound d.thetaB η θ z y E j hN hE hq hq1 hqhalf hσ.le hslack
  · exact hB N eps lam θ s hN heps (hepslt.trans_le (min_le_left _ _)) hl0 hl1 hθ hsB
  · intro i j hi hj hcol
    exact ((hp i j (Or.inl hi)).2 ⟨hi,hj,hcol⟩).trans (le_max_left _ _)
  · intro i j hcpt
    exact (hp i j hcpt).1

/-- Literal globalRoot wrapper on the original angular contour. -/
theorem original_actual_source_deleted_pairs (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ eta0 : ℝ, 0<eta0 ∧ ∀ eta : ℝ, 0<eta → eta<eta0 →
      ∃ alpha0 c e kappa : ℝ, ∃ B : ℕ → ℝ,
        0<alpha0 ∧ 0<c ∧ 0<e ∧ (∀ j,0<B j) ∧ 0<kappa ∧
        ∀ alpha : ℝ, 0<alpha → alpha<alpha0 →
        ∀ (N : ℕ) (eps : ℝ) (theta : Fin N → ℝ) (s : ℂ)
          (E : Finset (Fin N × Fin N)) (j : ℕ),
          1≤N → E.card≤j → 0<eps → eps<e → theta∈angleBox N →
          theta∈tsupport (angularSelector (constructedSelector d.thetaB eta alpha)) →
          ‖s-radialParameter d.theta eps‖≤c*eps →
          let y := angleTuple (Real.exp (-d.c₀*eps)) theta
          (∏ p ∈ orderedIndexPairs (Finset.univ : Finset (Fin N)) \ E,
            ‖canceledPair (y p.1) (y p.2) (globalRoot s (y p.1)) (globalRoot s (y p.2))‖) ≤
            (B j)^N*Real.exp (-kappa*(N:ℝ)^2) := by
  obtain ⟨eta0,he0,hmain⟩ := original_actual_deleted_pair_product d hcsmall
  have hsint : 0<Real.sin d.theta := Real.sin_pos_of_pos_of_lt_pi d.theta_pos
    (by linarith [d.theta_lt,Real.pi_pos])
  obtain ⟨cR,eR,hcR,_hcR1,heR,_heR1,hupper⟩ := original_disk_sourceW_upper d.theta d.c₀ hsint d.c₀_pos hcsmall
  refine ⟨eta0,he0,?_⟩
  intro eta he heL
  obtain ⟨alpha0,cP,eP,kappa,B,ha0,hcP,heP,hB,hk,hbound⟩ := hmain eta he heL
  refine ⟨alpha0,min cP cR,min eP eR,kappa,B,ha0,lt_min hcP hcR,lt_min heP heR,hB,hk,?_⟩
  intro alpha ha haL N eps theta s E j hN hE heps hepsL htheta hsupp hsd
  have hsP := hsd.trans (mul_le_mul_of_nonneg_right (min_le_left cP cR) heps.le)
  have hsR := hsd.trans (mul_le_mul_of_nonneg_right (min_le_right cP cR) heps.le)
  have hh := hbound alpha ha haL N eps theta s E j hN hE heps
    (hepsL.trans_le (min_le_left _ _)) htheta hsupp hsP
  have hroot (i : Fin N) : selectedContinuedRoot s (radialAnglePoint (-d.c₀*eps) (theta i))=
      globalRoot s (anglePoint (Real.exp (-d.c₀*eps)) (theta i)) := by
    have hW := hupper eps heps (hepsL.trans_le (min_le_right _ _)) s hsR (theta i)
    unfold selectedContinuedRoot globalRoot
    rw [continuedRoot_eq_interiorRoot hW,radialAnglePoint_eq_anglePoint]
  dsimp only at hh ⊢
  simp_rw [hroot,radialAnglePoint_eq_anglePoint] at hh
  exact hh

/-- Literal globalRoot wrapper for all coupled-current lambda values. -/
theorem original_current_actual_source_deleted_pairs (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ eta0 : ℝ, 0<eta0 ∧ ∀ eta : ℝ, 0<eta → eta<eta0 →
      ∃ alpha0 tau0 : ℝ, 0<alpha0 ∧ 0<tau0 ∧ ∀ alpha tau : ℝ,
        0<alpha → alpha<alpha0 → 0<tau → tau<tau0 →
        ∃ c e kappa : ℝ, ∃ B : ℕ → ℝ,
          0<c ∧ 0<e ∧ (∀ j,0<B j) ∧ 0<kappa ∧
          ∀ (N : ℕ) (eps lam : ℝ) (theta : Fin N → ℝ) (qidx : Fin N) (s : ℂ)
            (E : Finset (Fin N × Fin N)) (j : ℕ),
            E.card≤j → 1≤N → 0<eps → eps<e → 0≤lam → lam≤1 →
            theta∈angleBox N →
            theta∈tsupport (namedSelectorDerivative (constructedSelector d.thetaB eta alpha) qidx) →
            ‖s-radialParameter d.theta eps‖≤c*eps →
            let y := deformedPoint (constructedSelector d.thetaB eta alpha) (Real.exp (-d.c₀*eps)) tau lam theta
            (∏ p ∈ orderedIndexPairs (Finset.univ : Finset (Fin N)) \ E,
              ‖canceledPair (y p.1) (y p.2) (globalRoot s (y p.1)) (globalRoot s (y p.2))‖) ≤
              (B j)^N*Real.exp (-kappa*(N:ℝ)^2) := by
  obtain ⟨eta0,he0,hmain⟩ := original_current_actual_deleted_pair_product d hcsmall
  have hsint : 0<Real.sin d.theta := Real.sin_pos_of_pos_of_lt_pi d.theta_pos
    (by linarith [d.theta_lt,Real.pi_pos])
  obtain ⟨cR,eR,hcR,_hcR1,heR,_heR1,hupper⟩ := original_disk_sourceW_upper d.theta d.c₀ hsint d.c₀_pos hcsmall
  refine ⟨min eta0 (Real.sin d.thetaB/4),lt_min he0 (by positivity [d.a_pos]),?_⟩
  intro eta he heL
  obtain ⟨alpha0,tau0,ha0,ht0,hsetup⟩ := hmain eta he (heL.trans_le (min_le_left _ _))
  refine ⟨alpha0,tau0,ha0,ht0,?_⟩
  intro alpha tau ha haL ht htL
  obtain ⟨cP,eP,kappa,B,hcP,heP,hB,hk,hbound⟩ := hsetup alpha tau ha haL ht htL
  refine ⟨min cP cR,min eP eR,kappa,B,lt_min hcP hcR,lt_min heP heR,hB,hk,?_⟩
  intro N eps lam theta qidx s E j hE hN heps hepsL hl hl1 htheta hsupp hsd
  let f := constructedSelector d.thetaB eta alpha
  have hf : RegularSelector f := constructedSelector_regular d.thetaB eta alpha d.a_pos he
    (heL.le.trans (min_le_right _ _)) ha
  have hsP := hsd.trans (mul_le_mul_of_nonneg_right (min_le_left cP cR) heps.le)
  have hsR := hsd.trans (mul_le_mul_of_nonneg_right (min_le_right cP cR) heps.le)
  have hh := hbound N eps lam theta qidx s E j hE hN heps
    (hepsL.trans_le (min_le_left _ _)) hl hl1 htheta hsupp hsP
  have hroot (i : Fin N) : selectedContinuedRoot s (deformedPoint f (Real.exp (-d.c₀*eps)) tau lam theta i)=
      globalRoot s (deformedPoint f (Real.exp (-d.c₀*eps)) tau lam theta i) := by
    have hW0 := hupper eps heps (hepsL.trans_le (min_le_right _ _)) s hsR (theta i)
    have hW : 0<(sourceW s (deformedPoint f (Real.exp (-d.c₀*eps)) tau lam theta i)).im := by
      have hmono := deformed_sourceW_im_ge (by omega : 0<N) f (Real.exp_pos (-d.c₀*eps)) ht.le hl theta s
        hf.p_nonneg hf.m_nonneg hf.p_zero hf.m_zero i
      rw [deformedPoint_zero] at hmono
      rw [radialAnglePoint_eq_anglePoint] at hW0
      exact hW0.trans_le hmono
    unfold selectedContinuedRoot globalRoot
    exact continuedRoot_eq_interiorRoot hW
  dsimp only at hh ⊢
  dsimp [f] at hroot
  simp_rw [hroot] at hh
  exact hh

end
end IsingBulk.Tail
