import IsingBulk.Tail.OriginalPairSupport
import IsingBulk.Tail.ProtectedCompletePairProduct

/-! Full N-squared complete-pair suppression on the actual original K
closed support and original c epsilon disk, with no N-window restriction. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem original_actual_complete_pair_product (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η < η₀ →
      ∃ α₀ c e B κ : ℝ, 0 < α₀ ∧ 0 < c ∧ 0 < e ∧ 0 < B ∧ 0 < κ ∧
      ∀ α : ℝ, 0 < α → α < α₀ → ∀ (N : ℕ) (eps : ℝ) (θ : Fin N → ℝ) (s : ℂ),
        0 < eps → eps < e → θ ∈ angleBox N →
        θ ∈ tsupport (angularSelector (constructedSelector d.thetaB η α)) →
        ‖s-radialParameter d.theta eps‖ ≤ c*eps →
        let y := fun i => radialAnglePoint (-d.c₀*eps) (θ i)
        ‖canceledPairProduct (fun i => selectedContinuedRoot s (y i)) y‖ ≤
          B^N*Real.exp (-κ*(N:ℝ)^2) := by
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
  refine ⟨α₀,c,min eB (min r 1),Real.exp (-Real.log q/2),-Real.log q/12,
    lt_min hr (by positivity [d.a_pos]),lt_min hcB hr,lt_min heB (lt_min hr zero_lt_one),
    Real.exp_pos _,by linarith,?_⟩
  intro α hα hαlt N eps θ s heps hepslt hθ hsupp hsd
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
  apply complete_pair_chord_three_group_bound d.thetaB η θ z y hq hq1 hqhalf hσ.le hslack
  · intro i j hi hj
    exact hB η eps (θ i) (θ j) s hη hηlt heps (hepslt.trans_le (min_le_left _ _))
      (hθ.1 i) (hθ.2 i) (hθ.1 j) (hθ.2 j) hi hj
      (hsd.trans (mul_le_mul_of_nonneg_right (min_le_left cB r) heps.le))
  · intro i j hi hj hcol
    exact ((hp i j (Or.inl hi)).2 ⟨hi,hj,hcol⟩).trans (le_max_left _ _)
  · intro i j hcpt
    exact (hp i j hcpt).1

theorem radialAnglePoint_eq_anglePoint (v θ : ℝ) :
    radialAnglePoint v θ=anglePoint (Real.exp v) θ := by
  simp only [radialAnglePoint,Complex.exp_add,anglePoint,circleMap,zero_add]
  rw [Complex.ofReal_exp]

/-- Literal FIRST angular coordinates and literal source globalRoot. -/
theorem original_actual_source_pair_product (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η < η₀ →
      ∃ α₀ c e B κ : ℝ, 0 < α₀ ∧ 0 < c ∧ 0 < e ∧ 0 < B ∧ 0 < κ ∧
      ∀ α : ℝ, 0 < α → α < α₀ → ∀ (N : ℕ) (eps : ℝ) (θ : Fin N → ℝ) (s : ℂ),
        0 < eps → eps < e → θ ∈ angleBox N →
        θ ∈ tsupport (angularSelector (constructedSelector d.thetaB η α)) →
        ‖s-radialParameter d.theta eps‖ ≤ c*eps →
        let y := angleTuple (Real.exp (-d.c₀*eps)) θ
        ‖canceledPairProduct (fun i => globalRoot s (y i)) y‖ ≤
          B^N*Real.exp (-κ*(N:ℝ)^2) := by
  obtain ⟨η₀,hη₀,hpair⟩ := original_actual_complete_pair_product d hcsmall
  have hsint : 0 < Real.sin d.theta := Real.sin_pos_of_pos_of_lt_pi d.theta_pos
    (by linarith [d.theta_lt,Real.pi_pos])
  obtain ⟨cR,eR,hcR,_hcR1,heR,_heR1,hupper⟩ := original_disk_sourceW_upper d.theta d.c₀ hsint d.c₀_pos hcsmall
  refine ⟨η₀,hη₀,?_⟩
  intro η hη hηlt
  obtain ⟨α₀,cP,eP,B,κ,hα₀,hcP,heP,hB,hκ,hP⟩ := hpair η hη hηlt
  refine ⟨α₀,min cP cR,min eP eR,B,κ,hα₀,lt_min hcP hcR,lt_min heP heR,hB,hκ,?_⟩
  intro α hα hαlt N eps θ s heps hepslt hθ hsupp hsd
  have hsP := hsd.trans (mul_le_mul_of_nonneg_right (min_le_left cP cR) heps.le)
  have hsR := hsd.trans (mul_le_mul_of_nonneg_right (min_le_right cP cR) heps.le)
  have hh := hP α hα hαlt N eps θ s heps (hepslt.trans_le (min_le_left _ _)) hθ hsupp hsP
  have he (i : Fin N) : selectedContinuedRoot s (radialAnglePoint (-d.c₀*eps) (θ i))=
      globalRoot s (anglePoint (Real.exp (-d.c₀*eps)) (θ i)) := by
    have hW := hupper eps heps (hepslt.trans_le (min_le_right _ _)) s hsR (θ i)
    unfold selectedContinuedRoot globalRoot
    rw [continuedRoot_eq_interiorRoot hW,radialAnglePoint_eq_anglePoint]
  dsimp only at hh ⊢
  simp_rw [he] at hh
  change ‖canceledPairProduct (fun i => globalRoot s (anglePoint (Real.exp (-d.c₀*eps)) (θ i)))
    (fun i => anglePoint (Real.exp (-d.c₀*eps)) (θ i))‖ ≤ _
  simpa only [radialAnglePoint_eq_anglePoint] using hh


end
end IsingBulk.Tail
