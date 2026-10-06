import IsingBulk.Tail.MixedActiveResidualJets
import IsingBulk.Tail.MixedBranchChartNeighborhood
import IsingBulk.Tail.MixedActualResidualData

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem mixed_actual_active_data_jets (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (cap : ℝ) (hcap : 0<cap) (order : ℕ) :
    ∃ (inner : ℝ) (hi : 0< inner) (c e t₀ C : ℝ),inner≤cap ∧ 0<c ∧ 0<e ∧ 0<t₀ ∧ 0<C ∧
      ∀ η α : ℝ,0<η → η≤Real.sin d.thetaB/4 → 0<α →
      ∀ (N : ℕ) (eps τ lam : ℝ) (θ : Fin N → ℝ) (j q : Fin N)
        (sigma : Fin N → Fin 3) (l : List (Fin N)) (s : ℂ),
      1≤N → 0<eps → eps<e → 0≤τ → 0≤lam → lam≤1 → lam*τ<t₀ → θ∈angleBox N →
      sigma j=2 → sigma q≠2 →
      θ∈tsupport (IsingBulk.Jets.cutoffJet l (sectorAssignmentWeight d.thetaB inner hi sigma)) →
      ‖s-radialParameter d.theta eps‖≤c*eps →
      let y := deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam θ
      let φ := fun i => mixedSourcePhase s (y i)
      let V := mixedActiveResidualData (mixedBranchIndexSet sigma) j q s φ y
      AnalyticAt ℂ V 0 ∧ ∀ k≤order,‖iteratedFDeriv ℂ k V 0‖≤C := by
  let s₀ := radialParameter d.theta 0
  have hs₀ : s₀≠0 := norm_ne_zero_iff.mp (by
    change ‖radialParameter d.theta 0‖≠0
    rw [radialParameter_norm (by norm_num)]
    norm_num)
  have hS : s₀+s₀⁻¹=(1+(Real.cos d.thetaB:ℂ)) := by
    simpa [sourceS,s₀] using sourceS_radial_zero_branch d
  have hcos : |Real.cos d.thetaB|<1 := by
    have hsin : 0<Real.sin d.thetaB := d.a_pos
    rw [abs_lt]
    constructor <;> nlinarith [hsin,Real.sin_sq_add_cos_sq d.thetaB,
      Real.cos_le_one d.thetaB,Real.neg_one_le_cos d.thetaB]
  obtain ⟨U,hU,hUbase,hJets⟩ := mixed_active_residual_component_jets s₀ (Real.cos d.thetaB) hs₀ hS hcos order
  obtain ⟨inner,cB,eB,tB,hi,hicap,hcB,heB,htB,hBranch⟩ :=
    mixed_actual_branch_chart_neighborhood d hcsmall U hU hUbase cap hcap
  obtain ⟨K,cK,eK,tK,hK,hKD,hcK,heK,htK,hCompact⟩ := actual_compact_source_pair_set d inner hi
  obtain ⟨C,hC,hBound⟩ := hJets K hK hKD
  refine ⟨inner,hi,min cB cK,min eB eK,min tB tK,C,hicap,lt_min hcB hcK,
    lt_min heB heK,lt_min htB htK,hC,?_⟩
  intro η α hη hηsmall hα N eps τ lam θ j q sigma l s hN heps hepslt hτ hl0 hl1 htl hθ hσj hσq hsupp hs
  let J := mixedBranchIndexSet sigma
  let f := constructedSelector d.thetaB η α
  let y := deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ
  let φ := fun i => mixedSourcePhase s (y i)
  have hlabels := sector_assignment_cutoff_jets_support d.thetaB inner hi sigma l hsupp
  have hj : j∈J := by simp [J,mixedBranchIndexSet,hσj]
  have hq : q∉J := by simpa [J,mixedBranchIndexSet] using hσq
  have hBranchU (i : Fin N) (hiJ : i∈J) : (s,φ i)∈U := by
    have hσ : sigma i=2 := by simpa [J,mixedBranchIndexSet] using hiJ
    have hh := hlabels i
    rw [hσ] at hh
    exact hBranch η α hη hηsmall hα N eps τ lam θ i s hN heps
      (hepslt.trans_le (min_le_left _ _)) hτ hl0 hl1 (htl.trans_le (min_le_left _ _))
      (sector_branch_label_profile hi hh)
      (hs.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) heps.le))
  have hCompactK (i : Fin N) (hiJ : i∉J) : (s,y i)∈K := by
    have hσ : sigma i≠2 := by simpa [J,mixedBranchIndexSet] using hiJ
    exact hCompact f (fun x => thresholdStep_range _ _ _)
      (fun x => ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩)
      N eps τ lam θ i s hN heps.le (hepslt.le.trans (min_le_right _ _)) hτ hl0 hl1
      (htl.le.trans (min_le_right _ _)) ⟨hθ.1 i,hθ.2 i⟩
      (sector_compact_label_profile hi (sigma i) hσ (hlabels i))
      (hs.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) heps.le))
  obtain ⟨hAnalytic,hComponents⟩ := hBound N J j q s φ y (by omega) hj hq hBranchU hCompactK
  refine ⟨hAnalytic,?_⟩
  intro k hk
  obtain ⟨h₁,h₂,h₃,h₄⟩ := hComponents k hk
  exact analytic_four_components_jet_bound _ 0 hAnalytic k h₁ h₂ h₃ h₄

end
end IsingBulk.Tail
