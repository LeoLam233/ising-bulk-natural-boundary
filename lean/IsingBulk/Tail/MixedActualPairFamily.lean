import IsingBulk.Tail.MixedActivePairFamily

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem mixed_actual_sector_pair_family (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (cap : ℝ) (hcap : 0<cap) (order : ℕ) :
    ∃ inner₀ : ℝ,0< inner₀ ∧ inner₀≤cap ∧ ∀ (inner : ℝ) (hi : 0< inner),inner≤ inner₀ →
      ∃ c e t₀ C : ℝ,0<c ∧ 0<e ∧ 0<t₀ ∧ 0<C ∧
      ∀ η α : ℝ,0<η → η≤Real.sin d.thetaB/4 → 0<α → α<Real.sin d.thetaB/4 →
      ∀ (N : ℕ) (eps τ lam : ℝ) (θ : Fin N → ℝ) (q : Fin N)
        (sigma : Fin N → Fin 3) (l : List (Fin N)) (s : ℂ),
      1≤N → 0<eps → eps<e → 0≤τ → 0≤lam → lam≤1 → lam*τ<t₀ → θ∈angleBox N →
      (θ∈tsupport (angularSelector (constructedSelector d.thetaB η α)) ∨
        θ∈tsupport (namedSelectorDerivative (constructedSelector d.thetaB η α) q)) →
      θ∈tsupport (IsingBulk.Jets.cutoffJet l (sectorAssignmentWeight d.thetaB inner hi sigma)) →
      ‖s-radialParameter d.theta eps‖≤c*eps →
      let y := deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam θ
      let φ := fun i => mixedSourcePhase s (y i)
      let F := mixedActiveCompletePair (mixedBranchIndexSet sigma) q s φ y
      ∀ i j, F i j 0=canceledPair (y i) (y j) (globalRoot s (y i)) (globalRoot s (y j)) ∧
        AnalyticAt ℂ (F i j) 0 ∧ ∀ k≤order,‖iteratedFDeriv ℂ k (F i j) 0‖≤C := by
  let capAll := min cap ((Real.sin d.thetaB)^2/4)
  have hcapAll : 0<capAll := lt_min hcap (by positivity [d.a_pos])
  obtain ⟨inner₀,hi₀,hiCap,hFamily⟩ := mixed_actual_active_pair_family_jets d hcsmall capAll hcapAll order
  refine ⟨inner₀,hi₀,hiCap.trans (min_le_left _ _),?_⟩
  intro inner hi hinner
  obtain ⟨cF,eF,tF,C,hcF,heF,htF,hC,hFamily⟩ := hFamily inner hi hinner
  obtain ⟨cG,eG,tG,hcG,heG,htG,hGeometry⟩ := mixed_actual_uniform_source_data d hcsmall 1 zero_lt_one
  refine ⟨min cF cG,min eF eG,min tF tG,C,lt_min hcF hcG,lt_min heF heG,lt_min htF htG,hC,?_⟩
  intro η α hη hηsmall hα hαsmall N eps τ lam θ q sigma l s hN heps hepslt hτ hl0 hl1 htl hθ hSource hsupp hs
  let f := constructedSelector d.thetaB η α
  let y := deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ
  let φ := fun i => mixedSourcePhase s (y i)
  let J := mixedBranchIndexSet sigma
  have hlabels := sector_assignment_cutoff_jets_support d.thetaB inner hi sigma l hsupp
  have hBP (i : Fin N) (hiJ : i∈J) : |sectorDisplacement d.thetaB (θ i)|≤ inner := by
    have hσ : sigma i=2 := by simpa [J,mixedBranchIndexSet] using hiJ
    have hh := hlabels i
    rw [hσ] at hh
    exact sector_branch_label_profile hi hh
  have hCP (i : Fin N) (hiJ : i∉J) : inner/2≤|sectorDisplacement d.thetaB (θ i)| := by
    have hσ : sigma i≠2 := by simpa [J,mixedBranchIndexSet] using hiJ
    exact sector_compact_label_profile hi (sigma i) hσ (hlabels i)
  have hJets := hFamily η α hη hηsmall hα N eps τ lam θ J q s hN heps
    (hepslt.trans_le (min_le_left _ _)) hτ hl0 hl1 (htl.trans_le (min_le_left _ _)) hθ hBP hCP
    (hs.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) heps.le))
  obtain ⟨_,hcoords⟩ := hGeometry η α hη hηsmall hα N eps τ lam θ s hN heps
    (hepslt.trans_le (min_le_right _ _)) hτ hl0 hl1 (htl.trans_le (min_le_right _ _))
    (hs.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) heps.le))
  have hW (i : Fin N) : 0<(sourceW s (y i)).im := by
    obtain ⟨_,_,_,_,hh⟩ := hcoords i
    exact hh
  have his : inner≤(Real.sin d.thetaB)^2/4 := (hinner.trans hiCap).trans (min_le_right _ _)
  have hsin (i : Fin N) (hiJ : i∈J) : Real.sin (θ i)<0 :=
    mixed_source_branch_sine_negative d.thetaB η α inner d.a_pos hα hαsmall hi.le his θ i q (hBP i hiJ) hSource
  dsimp only
  intro i j
  exact ⟨mixedActiveCompletePair_source J q f (Real.exp_pos _) τ lam s θ hsin hW i j,hJets i j⟩

end
end IsingBulk.Tail
