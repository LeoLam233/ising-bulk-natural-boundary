import IsingBulk.Tail.LeftFrozenCompactJets
import IsingBulk.Tail.MixedActualResidualData

/-! Polynomial-N jets of the actual left-sector frozen-branch Z denominator.
True branch phases are fixed; only the parameter and one compact angle are
active. The source field identification is supplied by the left transport. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set
open scoped BigOperators Topology

def leftFrozenRootFamily {N : ℕ} (J : Finset (Fin N)) (q : Fin N) (s : ℂ) (y : Fin N → ℂ)
    (i : Fin N) (u : ℂ × ℂ) : ℂ :=
  if i∈J then selectedContinuedRoot s (y i) else rotatingCompactRoot s (y i) (decide (i=q)) u

def leftFrozenZ {N : ℕ} (J : Finset (Fin N)) (q : Fin N) (s : ℂ) (y : Fin N → ℂ)
    (u : ℂ × ℂ) : ℂ := ∏ i,leftFrozenRootFamily J q s y i u

@[simp] theorem leftFrozenRootFamily_zero {N : ℕ} (J : Finset (Fin N)) (q : Fin N)
    (s : ℂ) (y : Fin N → ℂ) (i : Fin N) :
    leftFrozenRootFamily J q s y i 0=selectedContinuedRoot s (y i) := by
  unfold leftFrozenRootFamily
  split_ifs <;> simp

theorem leftFrozenRootFamily_branch {N : ℕ} (J : Finset (Fin N)) (q : Fin N)
    (s : ℂ) (y : Fin N → ℂ) (i : Fin N) (hi : i∈J) :
    leftFrozenRootFamily J q s y i=(fun _ => selectedContinuedRoot s (y i)) := by
  funext u
  simp [leftFrozenRootFamily,hi]

theorem leftFrozenRootFamily_compact {N : ℕ} (J : Finset (Fin N)) (q : Fin N)
    (s : ℂ) (y : Fin N → ℂ) (i : Fin N) (hi : i∉J) :
    leftFrozenRootFamily J q s y i=rotatingCompactRoot s (y i) (decide (i=q)) := by
  funext u
  simp [leftFrozenRootFamily,hi]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
theorem left_actual_frozen_Z_reciprocal_jets (d : LocalBranchData)
    (hcsmall : d.c₀<Real.sin d.theta/2) (inner : ℝ) (hi : 0< inner) :
    ∃ c e t₀ : ℝ,0<c ∧ 0<e ∧ 0<t₀ ∧ ∀ Jorder : ℕ,∃ B : ℝ,0<B ∧
      ∀ η α : ℝ,0<η → η≤Real.sin d.thetaB/4 → 0<α →
      ∀ (N : ℕ) (eps τ lam : ℝ) (θ : Fin N → ℝ) (a q : Fin N)
        (sigma : Fin N → Fin 3) (l : List (Fin N)) (s : ℂ),
        1≤N → 0<eps → eps<e → 0≤τ → 0≤lam → lam≤1 → lam*τ<t₀ → θ∈angleBox N →
        sigma a=0 → sigma q≠2 →
        θ ∈ tsupport (IsingBulk.Jets.cutoffJet l (sectorAssignmentWeight d.thetaB inner hi sigma)) →
        ‖s-radialParameter d.theta eps‖≤c*eps → ∀ k≤Jorder,
        ‖iteratedFDeriv ℂ k (fun u : ℂ × ℂ =>
          (1-leftFrozenZ (mixedBranchIndexSet sigma) q s
            (deformedPoint (constructedSelector d.thetaB η α) (Real.exp (-d.c₀*eps)) τ lam θ) u)⁻¹) 0‖ ≤
          B*(N:ℝ)^k := by
  obtain ⟨cL,eL,tL,qL,hcL,heL,htL,hqL,hqL1,hLeft⟩ := left_actual_profile_Z_gap d hcsmall inner hi
  obtain ⟨K,cK,eK,tK,hK,hKD,hcK,heK,htK,hCover⟩ := actual_compact_source_pair_set d inner hi
  have hsint : 0<Real.sin d.theta := Real.sin_pos_of_pos_of_lt_pi d.theta_pos
    (by linarith [d.theta_lt,Real.pi_pos])
  obtain ⟨cG,eG,hcG,_hcG1,heG,_heG1,hmargin⟩ := original_disk_trace_margin d.theta d.c₀ hsint d.c₀_pos hcsmall
  let c := min cL (min cK cG)
  let e := min eL (min eK eG)
  let t₀ := min tL tK
  refine ⟨c,e,t₀,lt_min hcL (lt_min hcK hcG),lt_min heL (lt_min heK heG),lt_min htL htK,?_⟩
  intro Jorder
  obtain ⟨C,hC,hCompactJets⟩ := compact_rotating_root_uniform_jets K hK hKD Jorder
  obtain ⟨CR,hCR,hRecip⟩ := reciprocal_product_uniform_jets qL hqL1 Jorder
  let M := max 1 C
  have hM : 1≤M := le_max_left _ _
  have hM0 : 0<M := lt_of_lt_of_le zero_lt_one hM
  refine ⟨CR*M^Jorder,by positivity,?_⟩
  intro η α hη hηsmall hα N eps τ lam θ a q sigma l s hN heps hepslt hτ hl0 hl1 htl hθ hσa _hσq hsupp hs k hk
  let f := constructedSelector d.thetaB η α
  let y := deformedPoint f (Real.exp (-d.c₀*eps)) τ lam θ
  let J := mixedBranchIndexSet sigma
  have heL' := hepslt.trans_le (min_le_left _ _)
  have heK' := hepslt.le.trans ((min_le_right _ _).trans (min_le_left _ _))
  have heG' := hepslt.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hsL := hs.trans (mul_le_mul_of_nonneg_right (min_le_left cL _) heps.le)
  have hsK := hs.trans (mul_le_mul_of_nonneg_right ((min_le_right cL _).trans (min_le_left cK cG)) heps.le)
  have hsG := hs.trans (mul_le_mul_of_nonneg_right ((min_le_right cL _).trans (min_le_right cK cG)) heps.le)
  have hlabels := sector_assignment_cutoff_jets_support d.thetaB inner hi sigma l hsupp
  have hleft : inner/2≤sectorDisplacement d.thetaB (θ a) := by
    have hh := hlabels a
    rw [hσa] at hh
    have hfun : sectorLabel d.thetaB inner hi (0:Fin 3)=sectorLeft d.thetaB inner hi := by funext x; simp [sectorLabel]
    rw [hfun] at hh
    exact (sector_labels_tsupport d.thetaB inner hi).1 hh
  obtain ⟨hAll,hAnchor,_hProd,_hGap⟩ := hLeft η α hη hηsmall hα N eps τ lam θ a s hN heps heL'
    hτ hl0 hl1 (htl.trans_le (min_le_left _ _)) hleft hsL
  have hm : (Real.exp (-d.c₀*eps))⁻¹-Real.exp (-d.c₀*eps)<(sourceS s).im := by
    simpa only [neg_mul,Real.exp_neg,inv_inv] using hmargin eps heps heG' s hsG
  have hr : 0<Real.exp (-d.c₀*eps) := Real.exp_pos _
  have hr1 : Real.exp (-d.c₀*eps)<1 := Real.exp_lt_one_iff.mpr (by nlinarith [d.c₀_pos])
  have hphys (i : Fin N) : 0<(sourceW s (y i)).im := by
    have hb := sourceW_upper_of_margin hr hr1 hm (deformedPoint_zero_norm f hr.le τ θ i)
    exact hb.trans_le (deformed_sourceW_im_ge (by omega) f hr hτ hl0 θ s
      (fun x => (thresholdStep_range _ _ _).1) (fun x => Real.smoothTransition.nonneg _)
      (fun x hx => thresholdStep_zero (by linarith) (by linarith))
      (fun x hx => lowerM_zero_of_nonneg_sine d.thetaB η x d.a_pos hη hηsmall hx) i)
  have hRootEq (i : Fin N) : selectedContinuedRoot s (y i)=globalRoot s (y i) := continuedRoot_eq_interiorRoot (hphys i)
  have hCompact (i : Fin N) (hiJ : i∉J) : (s,y i)∈K := by
    have hσ : sigma i≠2 := by simpa only [J,mixedBranchIndexSet,Finset.mem_filter,Finset.mem_univ,true_and] using hiJ
    exact hCover f (fun x => thresholdStep_range _ _ _) (fun x => ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩)
      N eps τ lam θ i s hN heps.le heK' hτ hl0 hl1 (htl.le.trans (min_le_right _ _))
      ⟨hθ.1 i,hθ.2 i⟩ (sector_compact_label_profile hi (sigma i) hσ (hlabels i)) hsK
  have hfa (i : Fin N) : AnalyticAt ℂ (leftFrozenRootFamily J q s y i) 0 := by
    by_cases hiJ : i∈J
    · rw [leftFrozenRootFamily_branch J q s y i hiJ]
      exact analyticAt_const
    · rw [leftFrozenRootFamily_compact J q s y i hiJ]
      exact rotatingCompactRoot_analyticAt (hKD (hCompact i hiJ)) (decide (i=q))
  have hfj (i : Fin N) (m : ℕ) (hmJ : m≤Jorder) :
      ‖iteratedFDeriv ℂ m (leftFrozenRootFamily J q s y i) 0‖≤M^m := by
    cases m with
    | zero => simpa only [norm_iteratedFDeriv_zero,leftFrozenRootFamily_zero,hRootEq,pow_zero] using hAll i
    | succ m =>
      by_cases hiJ : i∈J
      · rw [leftFrozenRootFamily_branch J q s y i hiJ]
        rw [iteratedFDeriv_succ_const]
        simpa only [Pi.zero_apply,norm_zero] using (pow_nonneg hM0.le (m+1))
      · have hh := hCompactJets (s,y i) (hCompact i hiJ) (decide (i=q)) (m+1) hmJ
        have hp : M≤M^(m+1) := by simpa only [pow_one] using pow_le_pow_right₀ hM (show 1≤m+1 by omega)
        rw [leftFrozenRootFamily_compact J q s y i hiJ]
        exact hh.trans ((le_max_right 1 C).trans hp)
  have hanchor : ∃ ell : Fin N, ‖leftFrozenRootFamily J q s y ell 0‖≤qL :=
    ⟨a,by simpa only [leftFrozenRootFamily_zero,hRootEq] using hAnchor⟩
  have hh := hRecip (ℂ × ℂ) N M hM (leftFrozenRootFamily J q s y) 0 hfa hfj hanchor k hk
  change ‖iteratedFDeriv ℂ k (fun u => (1-∏ i,leftFrozenRootFamily J q s y i u)⁻¹) 0‖≤_
  apply hh.trans
  rw [mul_pow]
  have hp := pow_le_pow_right₀ hM hk
  nlinarith [mul_nonneg (show 0≤CR by positivity) (mul_nonneg (sub_nonneg.mpr hp) (pow_nonneg (Nat.cast_nonneg N) k))]

end
end IsingBulk.Tail
