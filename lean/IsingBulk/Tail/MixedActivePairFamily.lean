import IsingBulk.Tail.MixedActualActivePairs
import IsingBulk.Tail.MixedBranchPairs
import IsingBulk.Tail.MixedActualResidualCoreJets

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def mixedActiveCompletePair {N : ℕ} (J : Finset (Fin N)) (q : Fin N)
    (s : ℂ) (φ y : Fin N → ℂ) (i j : Fin N) : MixedActiveSpace N → ℂ :=
  if i∈J then
    if j∈J then mixedActiveBranchPair s φ i j
    else activeBranchCompactPair i q j s (φ i) (y j)
  else if j∈J then activeBranchCompactPair j q i s (φ j) (y i)
    else activeCompactPair q i j s (y i) (y j)

theorem mixedActiveCompletePair_source {N : ℕ} (J : Finset (Fin N)) (q : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hbranch : ∀ i∈J,Real.sin (θ i)<0)
    (hW : ∀ i,0<(sourceW s (deformedPoint f r τ lam θ i)).im) (i j : Fin N) :
    mixedActiveCompletePair J q s (fun i => mixedSourcePhase s (deformedPoint f r τ lam θ i))
      (deformedPoint f r τ lam θ) i j 0=
      canceledPair (deformedPoint f r τ lam θ i) (deformedPoint f r τ lam θ j)
        (globalRoot s (deformedPoint f r τ lam θ i)) (globalRoot s (deformedPoint f r τ lam θ j)) := by
  unfold mixedActiveCompletePair
  split_ifs with hi hj hj
  · simpa [mixedActiveBranchPair,mixedContourPhase] using mixed_actual_branch_pair_identification f hr τ lam s θ i j
      (hbranch i hi) (hbranch j hj) (hW i) (hW j)
  · rw [activeBranchCompactPair_formula]
    simp only [Prod.fst_zero,Prod.snd_zero,Pi.zero_apply,add_zero,ite_self,mul_zero,Complex.exp_zero,mul_one]
    exact mixed_actual_branch_compact_pair_identification f hr τ lam s θ i j (hbranch i hi) (hW j)
  · rw [activeBranchCompactPair_formula]
    simp only [Prod.fst_zero,Prod.snd_zero,Pi.zero_apply,add_zero,ite_self,mul_zero,Complex.exp_zero,mul_one]
    have hh := mixed_actual_branch_compact_pair_identification f hr τ lam s θ j i (hbranch j hj) (hW i)
    exact hh.trans (canceledPair_swap _ _ _ _)
  · rw [activeCompactPair_formula]
    simp only [Prod.fst_zero,Prod.snd_zero,add_zero,ite_self,mul_zero,Complex.exp_zero,mul_one]
    unfold mixedCompactPair
    rw [show selectedContinuedRoot s (deformedPoint f r τ lam θ i)=globalRoot s (deformedPoint f r τ lam θ i)
      from continuedRoot_eq_interiorRoot (hW i),
      show selectedContinuedRoot s (deformedPoint f r τ lam θ j)=globalRoot s (deformedPoint f r τ lam θ j)
      from continuedRoot_eq_interiorRoot (hW j)]


theorem mixed_actual_active_pair_family_jets (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (cap : ℝ) (hcap : 0<cap) (order : ℕ) :
    ∃ inner₀ : ℝ,0< inner₀ ∧ inner₀≤cap ∧ ∀ inner : ℝ,0< inner → inner≤ inner₀ →
      ∃ c e t₀ C : ℝ,0<c ∧ 0<e ∧ 0<t₀ ∧ 0<C ∧
      ∀ η α : ℝ,0<η → η≤Real.sin d.thetaB/4 → 0<α →
      ∀ (N : ℕ) (eps τ lam : ℝ) (θ : Fin N → ℝ) (J : Finset (Fin N)) (q : Fin N) (s : ℂ),
      1≤N → 0<eps → eps<e → 0≤τ → 0≤lam → lam≤1 → lam*τ<t₀ → θ∈angleBox N →
      (∀ i∈J,|sectorDisplacement d.thetaB (θ i)|≤ inner) →
      (∀ i∉J,inner/2≤|sectorDisplacement d.thetaB (θ i)|) →
      ‖s-radialParameter d.theta eps‖≤c*eps →
      let y := deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam θ
      let φ := fun i => mixedSourcePhase s (y i)
      ∀ i j,AnalyticAt ℂ (mixedActiveCompletePair J q s φ y i j) 0 ∧ ∀ l≤order,
      ‖iteratedFDeriv ℂ l (mixedActiveCompletePair J q s φ y i j) 0‖≤C := by
  obtain ⟨iB,cB,eB,tB,BB,hiB,hiBcap,hcB,heB,htB,hBB,hBranch⟩ :=
    mixed_actual_branch_branch_pair_jets d hcsmall cap hcap order
  obtain ⟨inner₀,hi₀,hi₀B,hBC⟩ := mixed_actual_active_branch_compact_pair_jets d hcsmall iB hiB order
  refine ⟨inner₀,hi₀,hi₀B.trans hiBcap,?_⟩
  intro inner hi hinner
  obtain ⟨cA,eA,tA,BA,hcA,heA,htA,hBA,hCross⟩ := hBC inner hi hinner
  obtain ⟨eC,tC,BC,heC,htC,hBCpos,hCompact⟩ := mixed_actual_active_compact_pair_jets d inner hi order
  let C := max BB (max BA BC)
  have hBBC : BB≤C := le_max_left _ _
  have hBAC : BA≤C := (le_max_left _ _).trans (le_max_right _ _)
  have hBCC : BC≤C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨min cB (min cA (1/4)),min eB (min eA eC),min tB (min tA tC),C,
    lt_min hcB (lt_min hcA (by norm_num)),lt_min heB (lt_min heA heC),
    lt_min htB (lt_min htA htC),hBB.trans_le hBBC,?_⟩
  intro η α hη hηsmall hα N eps τ lam θ J q s hN heps hepslt hτ hl0 hl1 htl hθ hBP hCP hs
  let f := constructedSelector d.thetaB η α
  let y := deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ
  let φ := fun i => mixedSourcePhase s (y i)
  have hBranchJets (i j : Fin N) (hiJ : i∈J) (hjJ : j∈J) :
      AnalyticAt ℂ (mixedActiveBranchPair s φ i j) 0 ∧ ∀ l≤order,
      ‖iteratedFDeriv ℂ l (mixedActiveBranchPair s φ i j) 0‖≤C := by
    obtain ⟨ha,hj⟩ := hBranch η α hη hηsmall hα N eps τ lam θ i j s hN heps
      (hepslt.trans_le (min_le_left _ _)) hτ hl0 hl1 (htl.trans_le (min_le_left _ _))
      ((hBP i hiJ).trans (hinner.trans hi₀B)) ((hBP j hjJ).trans (hinner.trans hi₀B))
      (hs.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) heps.le))
    refine ⟨(mixedActiveBranchPair_jet_bound s φ i j 0 ha).1,?_⟩
    intro l hl
    exact (mixedActiveBranchPair_jet_bound s φ i j l ha).2.trans ((hj l hl).trans hBBC)
  have hCrossJets (i j : Fin N) (hiJ : i∈J) (hjJ : j∉J) :
      AnalyticAt ℂ (activeBranchCompactPair i q j s (φ i) (y j)) 0 ∧ ∀ l≤order,
      ‖iteratedFDeriv ℂ l (activeBranchCompactPair i q j s (φ i) (y j)) 0‖≤C := by
    obtain ⟨ha,hj⟩ := hCross η α hη hηsmall hα N eps τ lam θ i q j s hN heps
      (hepslt.trans_le ((min_le_right _ _).trans (min_le_left _ _))) hτ hl0 hl1
      (htl.trans_le ((min_le_right _ _).trans (min_le_left _ _))) (hBP i hiJ) ⟨hθ.1 j,hθ.2 j⟩ (hCP j hjJ)
      (hs.trans (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) heps.le))
    exact ⟨ha,fun l hl => (hj l hl).trans hBAC⟩
  have hCompactJets (i j : Fin N) (hiJ : i∉J) (hjJ : j∉J) :
      AnalyticAt ℂ (activeCompactPair q i j s (y i) (y j)) 0 ∧ ∀ l≤order,
      ‖iteratedFDeriv ℂ l (activeCompactPair q i j s (y i) (y j)) 0‖≤C := by
    obtain ⟨ha,hj⟩ := hCompact f (fun x => thresholdStep_range _ _ _)
      (fun x => ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩)
      N eps τ lam θ q i j s hN heps.le
      (hepslt.le.trans ((min_le_right _ _).trans (min_le_right _ _))) hτ hl0 hl1
      (htl.le.trans ((min_le_right _ _).trans (min_le_right _ _))) hθ (hCP i hiJ) (hCP j hjJ)
      (hs.trans (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) heps.le))
    exact ⟨ha,fun l hl => (hj l hl).trans hBCC⟩
  dsimp only
  intro i j
  unfold mixedActiveCompletePair
  split_ifs with hiJ hjJ hjJ
  · exact hBranchJets i j hiJ hjJ
  · exact hCrossJets i j hiJ hjJ
  · exact hCrossJets j i hjJ hiJ
  · exact hCompactJets i j hiJ hjJ

end
end IsingBulk.Tail
