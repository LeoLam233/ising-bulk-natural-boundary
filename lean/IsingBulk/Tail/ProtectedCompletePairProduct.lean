import IsingBulk.Tail.ProtectedCompletePairTransfer
import IsingBulk.Tail.ProtectedActualBranchPairs
import IsingBulk.Tail.CurrentPairTransferInput
import IsingBulk.Tail.CompletePairSourceColor

/-! Source-attached N-squared suppression for ALL complete current pairs.
The fixed branch width precedes eta; endpoint and deformation widths follow
eta-dependent compact constants. No population certificate is assumed. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem protected_actual_complete_pair_product (d : LocalBranchData) :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η < η₀ →
      ∃ α₀ τ₀ : ℝ, 0 < α₀ ∧ 0 < τ₀ ∧ ∀ α τ : ℝ,
        0 < α → α < α₀ → 0 < τ → τ < τ₀ →
        ∃ c e B κ : ℝ, 0 < c ∧ 0 < e ∧ 0 < B ∧ 0 < κ ∧
        ∀ (N : ℕ) (eps lamStar lam : ℝ) (θ : Fin N → ℝ) (qidx : Fin N) (s : ℂ),
          1 ≤ N → 0 < eps → eps < e → 0 < lamStar → lamStar ≤ lam → lam ≤ 1 →
          θ ∈ angleBox N → θ ∈ tsupport (namedSelectorDerivative (constructedSelector d.thetaB η α) qidx) →
          ‖s-radialParameter d.theta eps‖ ≤ c*lamStar/(N:ℝ)^2 →
          let y := deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam θ
          ‖canceledPairProduct (fun i => selectedContinuedRoot s (y i)) y‖ ≤
            B^N*Real.exp (-κ*(N:ℝ)^2) := by
  obtain ⟨ηB,τB,hηB,hτB,hbranch⟩ := protected_actual_branch_pair_bound d
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
  obtain ⟨r,hr,_hr1,hinput⟩ := actual_current_pair_inputs d hδ
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
  refine ⟨c,min eB r,Real.exp (-Real.log q/2),-Real.log q/12,lt_min hcB hr,lt_min heB hr,
    Real.exp_pos _,by linarith,?_⟩
  intro N eps lamStar lam θ qidx s hN heps hepslt hls hl hl1 hθ hsupp hsd
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  have hn0 : (0:ℝ)<N := by linarith
  have hc : 0 < c := lt_min hcB hr
  have hrad : c*lamStar/(N:ℝ)^2 ≤ c/(N:ℝ) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hn0) hn0).mpr
    calc
      c*lamStar*(N:ℝ) ≤ c*1*(N:ℝ) := by gcongr; exact hl.trans hl1
      _ ≤ c*(N:ℝ)^2 := by nlinarith [mul_nonneg hc.le (sub_nonneg.mpr hn)]
  have hsB := hsd.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (min_le_left cB r) hls.le) (sq_nonneg (N:ℝ)))
  let f := constructedSelector d.thetaB η α
  let y := deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ
  let z := fun i => selectedContinuedRoot s (y i)
  have hsine := (constructed_current_support_geometry d.thetaB η α d.a_pos hη hηsmall hα qidx hsupp).2.2.2.1
  have hm (i : Fin N) := hinput N eps τ lam α c f θ s hN heps.le
    (hepslt.trans_le (min_le_right _ _)) hτ.le (hτlt.trans_le (min_le_right _ _))
    (hls.le.trans hl) hl1 hα.le hαr (min_le_right _ _)
    (fun x => thresholdStep_range _ _ _) (fun x => ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩)
    (hsd.trans hrad) i (hsine i)
  have hp (i j : Fin N) (hcompact : η^2/2 ≤ lowerChord d.thetaB (θ i) ∨ η^2/2 ≤ lowerChord d.thetaB (θ j)) :=
    htuple α (θ i) (θ j) hα.le hαch ⟨hθ.1 i,hθ.2 i⟩ ⟨hθ.1 j,hθ.2 j⟩
      (hsine i) (hsine j) hcompact (y i) (y j) (z i) (z j)
      (by simpa only [lowerCircleProjection,y,mul_comm] using (hm i).1)
      (by simpa only [lowerCircleProjection,y,mul_comm] using (hm j).1)
      (hm i).2 (hm j).2
  apply complete_pair_chord_three_group_bound d.thetaB η θ z y hq hq1 hqhalf hσ.le hslack
  · exact hB N eps lamStar lam θ qidx s hN heps (hepslt.trans_le (min_le_left _ _))
      hls hl hl1 hθ hsupp hsB
  · intro i j hi hj hcol
    exact ((hp i j (Or.inl hi)).2 ⟨hi,hj,hcol⟩).trans (le_max_left _ _)
  · intro i j hcpt
    exact (hp i j hcpt).1

end
end IsingBulk.Tail
