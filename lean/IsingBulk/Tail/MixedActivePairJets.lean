import IsingBulk.Tail.MixedCompactPairJets
import IsingBulk.Tail.MixedResidualCoreJets

namespace IsingBulk.Tail
noncomputable section
open Set Metric
open scoped Topology BigOperators ContDiff
attribute [local fun_prop] analyticAt_fst analyticAt_snd

abbrev PairScalarData := ℂ × ℂ × ℂ
abbrev PairLiftData := PairScalarData × ℂ

def pairLiftMap (left right : Bool) (p : PairLiftData) : PairScalarData :=
  (p.1.1, (if left then p.1.2.1*Complex.exp (Complex.I*p.2) else p.1.2.1),
    (if right then p.1.2.2*Complex.exp (Complex.I*p.2) else p.1.2.2))

@[simp] theorem pairLiftMap_zero (left right : Bool) (p : PairScalarData) :
    pairLiftMap left right (p,0)=p := by
  cases left <;> cases right <;> simp [pairLiftMap]

theorem pairLiftMap_analyticAt (left right : Bool) (p : PairLiftData) :
    AnalyticAt ℂ (pairLiftMap left right) p := by
  cases left <;> cases right <;> unfold pairLiftMap <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> fun_prop

theorem compact_finite_vector_analytic_jets {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (K : Set E) (hK : IsCompact K) (f : E → F) (hf : ∀ x∈K,AnalyticAt ℂ f x) (j : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ x∈K,∀ k≤j,‖iteratedFDeriv ℂ k f x‖≤C := by
  have hc (k : ℕ) : ContinuousOn (iteratedFDeriv ℂ k f) K := fun x hx =>
    ((hf x hx).contDiffAt.continuousAt_iteratedFDeriv (n := ⊤) (by simp)).continuousWithinAt
  have hb (k : ℕ) : ∃ C : ℝ,0<C ∧ ∀ x∈K,‖iteratedFDeriv ℂ k f x‖≤C := by
    obtain ⟨C,hC,hbound⟩ := (hK.image_of_continuousOn (hc k)).isBounded.exists_pos_norm_le
    exact ⟨C,hC,fun x hx => hbound _ ⟨x,hx,rfl⟩⟩
  choose C hC hbound using hb
  refine ⟨∑ k∈Finset.range (j+1),C k,Finset.sum_pos (fun k _ => hC k) ⟨0,by simp⟩,?_⟩
  intro x hx k hk
  exact (hbound k x hx).trans (Finset.single_le_sum (fun l _ => (hC l).le) (Finset.mem_range.mpr (by omega)))

theorem pair_lift_uniform_jets (M B : ℝ) (hB : 0<B) (order : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ (left right : Bool) (F : PairScalarData → ℂ) (p : PairScalarData),
      ‖p‖≤M → AnalyticAt ℂ F p → (∀ k≤order,‖iteratedFDeriv ℂ k F p‖≤B) →
      AnalyticAt ℂ (F ∘ pairLiftMap left right) (p,0) ∧ ∀ k≤order,
      ‖iteratedFDeriv ℂ k (F ∘ pairLiftMap left right) (p,0)‖≤C := by
  let K : Set PairLiftData := (fun p : PairScalarData => (p,(0:ℂ))) '' closedBall 0 M
  have hK : IsCompact K := (isCompact_closedBall 0 M).image (by fun_prop)
  have hb (left right : Bool) : ∃ C : ℝ,0<C ∧ ∀ p∈K,∀ k≤order,
      ‖iteratedFDeriv ℂ k (pairLiftMap left right) p‖≤C :=
    compact_finite_vector_analytic_jets K hK _ (fun p _ => pairLiftMap_analyticAt left right p) order
  choose D hD hDb using hb
  let L := max 1 (∑ l : Bool,∑ r : Bool,D l r)
  have hL : 1≤L := le_max_left _ _
  have hL0 : 0<L := zero_lt_one.trans_le hL
  have hDL (l r : Bool) : D l r≤L := by
    apply le_trans _ (le_max_right _ _)
    exact (Finset.single_le_sum (fun t _ => (hD l t).le) (Finset.mem_univ r)).trans
      (Finset.single_le_sum (fun t _ => Finset.sum_nonneg (fun u _ => (hD t u).le)) (Finset.mem_univ l))
  refine ⟨order.factorial*B*L^order,by positivity,?_⟩
  intro left right F p hp hF hFj
  have ha := pairLiftMap_analyticAt left right (p,0)
  have hF' : AnalyticAt ℂ F (pairLiftMap left right (p,0)) := by simpa using hF
  refine ⟨hF'.comp ha,?_⟩
  intro k hk
  have hj : ∀ i,1≤ i → i≤k → ‖iteratedFDeriv ℂ i (pairLiftMap left right) (p,0)‖≤L^i := by
    intro i hi hik
    exact (hDb left right (p,0) ⟨p,by simpa [mem_closedBall,dist_eq_norm] using hp,rfl⟩ i (hik.trans hk)).trans
      ((hDL left right).trans (by simpa only [pow_one] using pow_le_pow_right₀ hL hi))
  have hh := analytic_vector_composition_geometric_jets F (pairLiftMap left right) (p,0) k hF' ha B L
    (by simpa only [pairLiftMap_zero] using (fun i hi => hFj i (hi.trans hk))) hj
  exact hh.trans (by gcongr)


def branchCompactPairEmbedding {N : ℕ} (j : Fin N) : MixedActiveSpace N →L[ℂ] PairLiftData :=
  ((ContinuousLinearMap.fst ℂ ℂ ((Fin N → ℂ) × ℂ)).prod
    (((ContinuousLinearMap.proj (R := ℂ) j).comp
      ((ContinuousLinearMap.fst ℂ (Fin N → ℂ) ℂ).comp
        (ContinuousLinearMap.snd ℂ ℂ ((Fin N → ℂ) × ℂ)))).prod 0)).prod
    ((ContinuousLinearMap.snd ℂ (Fin N → ℂ) ℂ).comp
      (ContinuousLinearMap.snd ℂ ℂ ((Fin N → ℂ) × ℂ)))

def compactPairEmbedding (N : ℕ) : MixedActiveSpace N →L[ℂ] PairLiftData :=
  ((ContinuousLinearMap.fst ℂ ℂ ((Fin N → ℂ) × ℂ)).prod 0).prod
    ((ContinuousLinearMap.snd ℂ (Fin N → ℂ) ℂ).comp
      (ContinuousLinearMap.snd ℂ ℂ ((Fin N → ℂ) × ℂ)))

theorem branchCompactPairEmbedding_norm {N : ℕ} (j : Fin N) : ‖branchCompactPairEmbedding j‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  change ‖((u.1,(u.2.1 j,0)),u.2.2)‖≤1*‖u‖
  simp only [one_mul,Prod.norm_def,norm_zero,max_eq_left (norm_nonneg _)]
  have hb : ‖u.2.1 j‖≤max ‖u.1‖ (max ‖u.2.1‖ ‖u.2.2‖) := (norm_le_pi_norm u.2.1 j).trans ((le_max_left _ _).trans (le_max_right _ _))
  exact max_le (max_le (le_max_left _ _) hb) ((le_max_right _ _).trans (le_max_right _ _))

theorem compactPairEmbedding_norm (N : ℕ) : ‖compactPairEmbedding N‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  change ‖((u.1,(0,0)),u.2.2)‖≤1*‖u‖
  simp only [one_mul,Prod.norm_def,norm_zero,max_self,max_eq_left (norm_nonneg _)]
  exact max_le (le_max_left _ _) ((le_max_right _ _).trans (le_max_right _ _))

def activeBranchCompactPair {N : ℕ} (j q k : Fin N) (s φ y : ℂ) (u : MixedActiveSpace N) : ℂ :=
  (mixedBranchCompactPair ∘ pairLiftMap false (decide (k=q)))
    (branchCompactPairEmbedding j u+((s,φ,y),0))

def activeCompactPair {N : ℕ} (q i j : Fin N) (s y v : ℂ) (u : MixedActiveSpace N) : ℂ :=
  (mixedCompactPair ∘ pairLiftMap (decide (i=q)) (decide (j=q)))
    (compactPairEmbedding N u+((s,y,v),0))

theorem active_pair_jets_of_scalar (M B : ℝ) (hB : 0<B) (order : ℕ) :
    ∃ C : ℝ,0<C ∧ ∀ (N : ℕ) (j q k : Fin N) (p : PairScalarData),‖p‖≤M →
      (AnalyticAt ℂ mixedBranchCompactPair p →
        (∀ l≤order,‖iteratedFDeriv ℂ l mixedBranchCompactPair p‖≤B) →
        AnalyticAt ℂ (activeBranchCompactPair j q k p.1 p.2.1 p.2.2) 0 ∧ ∀ l≤order,
        ‖iteratedFDeriv ℂ l (activeBranchCompactPair j q k p.1 p.2.1 p.2.2) 0‖≤C) ∧
      (AnalyticAt ℂ mixedCompactPair p →
        (∀ l≤order,‖iteratedFDeriv ℂ l mixedCompactPair p‖≤B) →
        AnalyticAt ℂ (activeCompactPair q j k p.1 p.2.1 p.2.2) 0 ∧ ∀ l≤order,
        ‖iteratedFDeriv ℂ l (activeCompactPair q j k p.1 p.2.1 p.2.2) 0‖≤C) := by
  obtain ⟨C,hC,hLift⟩ := pair_lift_uniform_jets M B hB order
  refine ⟨C,hC,?_⟩
  intro N j q k p hp
  constructor
  · intro ha hj
    obtain ⟨hA,hJ⟩ := hLift false (decide (k=q)) mixedBranchCompactPair p hp ha hj
    have hA' : AnalyticAt ℂ (mixedBranchCompactPair ∘ pairLiftMap false (decide (k=q)))
        (branchCompactPairEmbedding j 0+(p,0)) := by simpa using hA
    refine ⟨hA'.comp (f := fun u => branchCompactPairEmbedding j u+(p,0))
      (((branchCompactPairEmbedding j).analyticAt 0).add analyticAt_const),?_⟩
    intro l hl
    exact (analytic_affine_pullback_jet_norm (branchCompactPairEmbedding j) _ (p,0) 0 hA'
      (branchCompactPairEmbedding_norm j) l).trans (by simpa using hJ l hl)
  · intro ha hj
    obtain ⟨hA,hJ⟩ := hLift (decide (j=q)) (decide (k=q)) mixedCompactPair p hp ha hj
    have hA' : AnalyticAt ℂ (mixedCompactPair ∘ pairLiftMap (decide (j=q)) (decide (k=q)))
        (compactPairEmbedding N 0+(p,0)) := by simpa using hA
    refine ⟨hA'.comp (f := fun u => compactPairEmbedding N u+(p,0))
      (((compactPairEmbedding N).analyticAt 0).add analyticAt_const),?_⟩
    intro l hl
    exact (analytic_affine_pullback_jet_norm (compactPairEmbedding N) _ (p,0) 0 hA'
      (compactPairEmbedding_norm N) l).trans (by simpa using hJ l hl)


theorem activeBranchCompactPair_formula {N : ℕ} (j q k : Fin N) (s φ y : ℂ) (u : MixedActiveSpace N) :
    activeBranchCompactPair j q k s φ y u=
      mixedBranchCompactPair (s+u.1,φ+u.2.1 j,y*Complex.exp (Complex.I*(if k=q then u.2.2 else 0))) := by
  by_cases hk : k=q <;> simp [activeBranchCompactPair,pairLiftMap,branchCompactPairEmbedding,hk,add_comm]

theorem activeCompactPair_formula {N : ℕ} (q i j : Fin N) (s y v : ℂ) (u : MixedActiveSpace N) :
    activeCompactPair q i j s y v u=mixedCompactPair
      (s+u.1,y*Complex.exp (Complex.I*(if i=q then u.2.2 else 0)),
        v*Complex.exp (Complex.I*(if j=q then u.2.2 else 0))) := by
  by_cases hi : i=q <;> by_cases hj : j=q <;>
    simp [activeCompactPair,pairLiftMap,compactPairEmbedding,hi,hj,add_comm]

end
end IsingBulk.Tail
