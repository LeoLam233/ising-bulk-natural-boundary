import IsingBulk.Tail.OriginalCompletePairProduct
import IsingBulk.Tail.OriginalCurrentCompletePair

/-! Actual original and full-homotopy complete-pair Gaussian suppression
with finitely many factors deleted. The deletion cost is explicit and the
constants are chosen before the particle number and the deleted set. -/
namespace IsingBulk.HT.Lie
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail Set Filter
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem onsite_deleted_chord_pair_bound {N : ℕ} (b η : ℝ)
    (θ : Fin N → ℝ) (z y : Fin N → ℂ)
    (E : Finset (Fin N × Fin N)) (J : ℕ) (hE : E.card ≤ J) {q σ : ℝ}
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
      Real.exp (-J*Real.log q)*(Real.exp (-Real.log q/2))^N*
        Real.exp (-(-Real.log q/12)*(N:ℝ)^2) := by
  apply complete_pair_deleted_three_group_bound z y
    (fun i => completePairSourceColor b η (θ i)) E J hE hq hq1 hσ hslack
  · intro i j he
    rcases completePairSourceColor_eq_cases he with hB' | hC'
    · exact (hB i j hB'.1 hB'.2).trans hhalf
    · exact hC i j hC'.1 hC'.2.1 hC'.2.2
  · intro i j he
    exact hX i j (completePairSourceColor_ne_compact he)

theorem onsite_original_deleted_complete_pairs (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η < η₀ →
      ∃ α₀ c e B κ L : ℝ, 0 < α₀ ∧ 0 < c ∧ 0 < e ∧ 0 < B ∧ 0 < κ ∧ 0 < L ∧
      ∀ α : ℝ, 0 < α → α < α₀ → ∀ (N : ℕ) (eps : ℝ) (θ : Fin N → ℝ) (s : ℂ),
        0 < eps → eps < e → θ ∈ angleBox N →
        θ ∈ tsupport (angularSelector (constructedSelector d.thetaB η α)) →
        ‖s-radialParameter d.theta eps‖ ≤ c*eps →
        ∀ (E : Finset (Fin N × Fin N)) (J : ℕ), E.card ≤ J →
        let y := fun i => radialAnglePoint (-d.c₀*eps) (θ i)
        (∏ p ∈ orderedIndexPairs (Finset.univ : Finset (Fin N)) \ E,
          ‖canceledPair (y p.1) (y p.2)
            (selectedContinuedRoot s (y p.1)) (selectedContinuedRoot s (y p.2))‖) ≤
          Real.exp (L*J)*B^N*Real.exp (-κ*(N:ℝ)^2) := by
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
  refine ⟨α₀,c,min eB (min r 1),Real.exp (-Real.log q/2),-Real.log q/12,-Real.log q,
    lt_min hr (by positivity [d.a_pos]),lt_min hcB hr,lt_min heB (lt_min hr zero_lt_one),
    Real.exp_pos _,by linarith,by linarith,?_⟩
  intro α hα hαlt N eps θ s heps hepslt hθ hsupp hsd E J hE
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
  have hexp : (-Real.log q)*(J:ℝ) = -(J:ℝ)*Real.log q := by ring
  rw [hexp]
  apply onsite_deleted_chord_pair_bound d.thetaB η θ z y E J hE hq hq1 hqhalf hσ.le hslack
  · intro i j hi hj
    exact hB η eps (θ i) (θ j) s hη hηlt heps (hepslt.trans_le (min_le_left _ _))
      (hθ.1 i) (hθ.2 i) (hθ.1 j) (hθ.2 j) hi hj
      (hsd.trans (mul_le_mul_of_nonneg_right (min_le_left cB r) heps.le))
  · intro i j hi hj hcol
    exact ((hp i j (Or.inl hi)).2 ⟨hi,hj,hcol⟩).trans (le_max_left _ _)
  · intro i j hcpt
    exact (hp i j hcpt).1

theorem onsite_current_deleted_complete_pairs (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η < η₀ →
      ∃ α₀ τ₀ : ℝ, 0 < α₀ ∧ 0 < τ₀ ∧ ∀ α τ : ℝ,
        0 < α → α < α₀ → 0 < τ → τ < τ₀ →
        ∃ c e B κ L : ℝ, 0 < c ∧ 0 < e ∧ 0 < B ∧ 0 < κ ∧ 0 < L ∧
        ∀ (N : ℕ) (eps lam : ℝ) (θ : Fin N → ℝ) (qidx : Fin N) (s : ℂ),
          1 ≤ N → 0 < eps → eps < e → 0 ≤ lam → lam ≤ 1 →
          θ ∈ angleBox N → θ ∈ tsupport (namedSelectorDerivative (constructedSelector d.thetaB η α) qidx) →
          ‖s-radialParameter d.theta eps‖ ≤ c*eps →
          ∀ (E : Finset (Fin N × Fin N)) (J : ℕ), E.card ≤ J →
          let y := deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam θ
          (∏ p ∈ orderedIndexPairs (Finset.univ : Finset (Fin N)) \ E,
            ‖canceledPair (y p.1) (y p.2)
              (selectedContinuedRoot s (y p.1)) (selectedContinuedRoot s (y p.2))‖) ≤
            Real.exp (L*J)*B^N*Real.exp (-κ*(N:ℝ)^2) := by
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
  refine ⟨c,min eB r,Real.exp (-Real.log q/2),-Real.log q/12,-Real.log q,lt_min hcB hr,lt_min heB hr,
    Real.exp_pos _,by linarith,by linarith,?_⟩
  intro N eps lam θ qidx s hN heps hepslt hl0 hl1 hθ hsupp hsd E J hE
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
  have hexp : (-Real.log q)*(J:ℝ) = -(J:ℝ)*Real.log q := by ring
  rw [hexp]
  apply onsite_deleted_chord_pair_bound d.thetaB η θ z y E J hE hq hq1 hqhalf hσ.le hslack
  · exact hB N eps lam θ s hN heps (hepslt.trans_le (min_le_left _ _)) hl0 hl1 hθ hsB
  · intro i j hi hj hcol
    exact ((hp i j (Or.inl hi)).2 ⟨hi,hj,hcol⟩).trans (le_max_left _ _)
  · intro i j hcpt
    exact (hp i j hcpt).1

end
end IsingBulk.HT.Lie
