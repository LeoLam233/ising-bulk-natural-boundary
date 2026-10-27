import IsingBulk.Preferred22.CollectiveBounds

/-! The actual collective field preserves every pair diagonal. The explicit
factor is regular at partial collisions; only the original full-equality
R denominator remains. This is the source finite-block Vandermonde route. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set Filter
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

/-- A genuine divided difference of the actual collective pair extension. -/
def preferredCollectivePairDifference (s q r z : ℂ) : ℂ :=
  dslope (fun x => preferredCollectivePairExtension s x z) r q

/-- The coefficient of qi-qj in the actual field difference. The denominator
R is evaluated at the complete original configuration, never along a pair
transposition path. -/
def preferredCollectiveDifferenceFactor {N : ℕ} (s : ℂ) (q : Fin N → ℂ) (i j : Fin N) : ℂ :=
  (collectiveResidual (fun a => preferredSourceUDot s (q a))
      (fun a => preferredSourceUQ s (q a)) (-deriv preferredMovingBranch s) /
    collectiveDenominator (fun a => preferredMovingInverse s (q a))) *
      ∑ a,preferredCollectivePairDifference s (q i) (q j) (q a)

/-- Exact source pair-diagonal preservation, including qi=qj. -/
theorem preferredResidualCollective_difference_factor {N : ℕ} (s : ℂ)
    (q : Fin N → ℂ) (i j : Fin N) :
    preferredResidualCollective s q i-preferredResidualCollective s q j=
      (q i-q j)*preferredCollectiveDifferenceFactor s q i j := by
  have hp (a : Fin N) :
      preferredCollectivePairExtension s (q i) (q a)-preferredCollectivePairExtension s (q j) (q a)=
      (q i-q j)*preferredCollectivePairDifference s (q i) (q j) (q a) := by
    simpa only [preferredCollectivePairDifference,smul_eq_mul] using
      (sub_smul_dslope (fun x => preferredCollectivePairExtension s x (q a)) (q j) (q i)).symm
  unfold preferredResidualCollective collectiveField preferredCollectiveDifferenceFactor
  simp_rw [preferred_collectivePair_eq_extension]
  rw [show (-(deriv preferredMovingBranch s)+
      collectiveResidual (fun a => preferredSourceUDot s (q a)) (fun a => preferredSourceUQ s (q a)) (-deriv preferredMovingBranch s) /
      collectiveDenominator (fun a => preferredMovingInverse s (q a)) *
      (∑ a,preferredCollectivePairExtension s (q i) (q a))) -
      (-(deriv preferredMovingBranch s)+
      collectiveResidual (fun a => preferredSourceUDot s (q a)) (fun a => preferredSourceUQ s (q a)) (-deriv preferredMovingBranch s) /
      collectiveDenominator (fun a => preferredMovingInverse s (q a)) *
      (∑ a,preferredCollectivePairExtension s (q j) (q a))) =
      collectiveResidual (fun a => preferredSourceUDot s (q a)) (fun a => preferredSourceUQ s (q a)) (-deriv preferredMovingBranch s) /
      collectiveDenominator (fun a => preferredMovingInverse s (q a)) *
      ((∑ a,preferredCollectivePairExtension s (q i) (q a))-(∑ a,preferredCollectivePairExtension s (q j) (q a))) by ring]
  rw [←Finset.sum_sub_distrib]
  simp_rw [hp]
  rw [←Finset.mul_sum]
  ring

/-- Primitive factor norm: the actual residual, original R margin and
regular four-point divided difference give the exact inverse-square scale. -/
theorem preferredCollectiveDifferenceFactor_bound {N : ℕ} (s : ℂ)
    (q : Fin N → ℂ) (i j : Fin N) {L M c d : ℝ}
    (hL : 0≤L) (_hM : 0≤M) (hc : 0<c) (hd : 0<d)
    (hres : ‖collectiveResidual (fun a => preferredSourceUDot s (q a))
      (fun a => preferredSourceUQ s (q a)) (-deriv preferredMovingBranch s)‖≤(N:ℝ)*L)
    (hR : c*d^2≤‖collectiveDenominator (fun a => preferredMovingInverse s (q a))‖)
    (hpair : ∀ a,‖preferredCollectivePairDifference s (q i) (q j) (q a)‖≤M) :
    ‖preferredCollectiveDifferenceFactor s q i j‖≤L*M*(N:ℝ)^2/(c*d^2) := by
  have hsum : ‖∑ a,preferredCollectivePairDifference s (q i) (q j) (q a)‖≤(N:ℝ)*M :=
    (norm_sum_le _ _).trans (by simpa using Finset.sum_le_sum (s := Finset.univ) (fun a _ => hpair a))
  unfold preferredCollectiveDifferenceFactor
  rw [norm_mul,norm_div]
  calc
    _ ≤ ((N:ℝ)*L/(c*d^2))*((N:ℝ)*M) :=
      mul_le_mul (div_le_div₀ (by positivity) hres (by positivity) hR) hsum (norm_nonneg _) (by positivity)
    _ = _ := by ring


/-- The actual pair-difference coefficient is jointly analytic in its four
arguments, including every partial diagonal. -/
theorem preferredCollectivePairDifference_analyticAt (s q r z : ℂ)
    (D : Set ℂ) (c : ℝ) (hc : 0<c) (hD : Convex ℝ D)
    (hU : ∀ a∈D,AnalyticAt ℂ (fun x : ℂ × ℂ => preferredMovingInverse x.1 x.2) (s,a))
    (hcurv : ∀ a∈D,c≤(deriv (preferredSourceUQ s) a).re)
    (hq : q∈D) (hr : r∈D) (hz : z∈D) :
    AnalyticAt ℂ (fun x : ((ℂ × ℂ) × ℂ) × ℂ =>
      preferredCollectivePairDifference x.1.1.1 x.2 x.1.2 x.1.1.2) (((s,z),r),q) := by
  let F := fun x : ((ℂ × ℂ) × ℂ) × ℂ => preferredCollectivePairExtension x.1.1.1 x.2 x.1.1.2
  have hFq : AnalyticAt ℂ F (((s,z),r),q) :=
    AnalyticAt.comp
      (f := fun x : ((ℂ × ℂ) × ℂ) × ℂ => (x.1.1,x.2))
      (g := fun x : (ℂ × ℂ) × ℂ => preferredCollectivePairExtension x.1.1 x.2 x.1.2)
      (preferredCollectivePairExtension_analyticAt_of_curvature s q z D c hc hD hU hcurv hq hz)
      ((analyticAt_fst.comp analyticAt_fst).prod analyticAt_snd)
  have hFr : AnalyticAt ℂ F (((s,z),r),r) :=
    AnalyticAt.comp
      (f := fun x : ((ℂ × ℂ) × ℂ) × ℂ => (x.1.1,x.2))
      (g := fun x : (ℂ × ℂ) × ℂ => preferredCollectivePairExtension x.1.1 x.2 x.1.2)
      (preferredCollectivePairExtension_analyticAt_of_curvature s r z D c hc hD hU hcurv hr hz)
      ((analyticAt_fst.comp analyticAt_fst).prod analyticAt_snd)
  exact analyticAt_moving_dslope (F := F) (T := fun x : (ℂ × ℂ) × ℂ => x.2)
    hFq hFr analyticAt_snd

/-- A genuine compact bound for the four-argument divided difference. No
coefficient or differentiated-density bound is assumed. -/
theorem preferred_compact_collective_pair_difference (d : PreferredBranchData)
    (ρ c : ℝ) (D : Set ℂ) (hρ : 0<ρ) (hc : 0<c) (hDc : IsCompact D) (hDv : Convex ℝ D)
    (hg : ∀ s q r : ℂ,‖s-preferredSelectedPoint d‖<ρ → q∈D → r∈D →
      PreferredRightRegularPoint c s q r) :
    ∃ M : ℝ,1≤M ∧ ∀ s q r z : ℂ,‖s-preferredSelectedPoint d‖≤ρ/2 → q∈D → r∈D → z∈D →
      ‖preferredCollectivePairDifference s q r z‖≤M := by
  let X := ((Metric.closedBall (preferredSelectedPoint d) (ρ/2) ×ˢ D) ×ˢ D) ×ˢ D
  let F := fun x : ((ℂ × ℂ) × ℂ) × ℂ =>
    preferredCollectivePairDifference x.1.1.1 x.2 x.1.2 x.1.1.2
  have hX : IsCompact X := (((isCompact_closedBall _ _).prod hDc).prod hDc).prod hDc
  have hF : ContinuousOn F X := by
    intro x hx
    have hs : ‖x.1.1.1-preferredSelectedPoint d‖≤ρ/2 := by
      simpa only [Metric.mem_closedBall,dist_eq_norm] using hx.1.1.1
    exact (preferredCollectivePairDifference_analyticAt x.1.1.1 x.2 x.1.2 x.1.1.2 D c hc hDv
      (fun a ha => (hg _ a a (by linarith) ha ha).2.1)
      (fun a ha => by
        have hh := (hg x.1.1.1 a a (by linarith) ha ha).2.2.2.1.le
        change c≤(deriv (deriv (preferredMovingInverse x.1.1.1)) a).re
        rw [←preferredMovingCurvature_eq_deriv _ _ (hg _ a a (by linarith) ha ha).2.1]
        exact hh)
      hx.2 hx.1.2 hx.1.1.2).continuousAt.continuousWithinAt
  obtain ⟨A,hA⟩ := hX.exists_bound_of_continuousOn hF
  refine ⟨max A 1,le_max_right _ _,?_⟩
  intro s q r z hs hq hr hz
  exact (hA (((s,z),r),q) ⟨⟨⟨by simpa only [Metric.mem_closedBall,dist_eq_norm] using hs,hz⟩,hr⟩,hq⟩).trans
    (le_max_left _ _)


/-- The original complete-configuration R is the only excluded denominator
in the jointly analytic pair-diagonal factor. -/
theorem preferredCollectiveDifferenceFactor_analyticAt_of_curvature {N : ℕ}
    (s : ℂ) (q : Fin N → ℂ) (i j : Fin N) (D : Set ℂ) (c : ℝ)
    (hc : 0<c) (hD : Convex ℝ D)
    (hU : ∀ z∈D,AnalyticAt ℂ (fun x : ℂ × ℂ => preferredMovingInverse x.1 x.2) (s,z))
    (hB : AnalyticAt ℂ preferredMovingBranch s)
    (hcurv : ∀ z∈D,c≤(deriv (preferredSourceUQ s) z).re)
    (hq : ∀ a,q a∈D)
    (hR : collectiveDenominator (fun a => preferredMovingInverse s (q a))≠0) :
    AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => preferredCollectiveDifferenceFactor z.1 z.2 i j) (s,q) := by
  have hcoord (a : Fin N) : AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => z.2 a) (s,q) :=
    (((ContinuousLinearMap.proj a : (Fin N → ℂ) →L[ℂ] ℂ).comp
      (ContinuousLinearMap.snd ℂ ℂ (Fin N → ℂ))).analyticAt (s,q))
  have hu (a : Fin N) : AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => preferredMovingInverse z.1 (z.2 a)) (s,q) :=
    AnalyticAt.comp (f := fun z : ℂ × (Fin N → ℂ) => (z.1,z.2 a))
      (g := fun z : ℂ × ℂ => preferredMovingInverse z.1 z.2) (hU (q a) (hq a))
      (analyticAt_fst.prod (hcoord a))
  have hv (a : Fin N) : AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => preferredSourceUQ z.1 (z.2 a)) (s,q) :=
    AnalyticAt.comp (f := fun z : ℂ × (Fin N → ℂ) => (z.1,z.2 a))
      (g := fun z : ℂ × ℂ => preferredSourceUQ z.1 z.2)
      (preferredSourceUQ_analyticAt_of_joint s (q a) (hU _ (hq a))) (analyticAt_fst.prod (hcoord a))
  have hd (a : Fin N) : AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => preferredSourceUDot z.1 (z.2 a)) (s,q) :=
    AnalyticAt.comp (f := fun z : ℂ × (Fin N → ℂ) => (z.1,z.2 a))
      (g := fun z : ℂ × ℂ => preferredSourceUDot z.1 z.2)
      (preferredSourceUDot_analyticAt_of_joint s (q a) (hU _ (hq a))) (analyticAt_fst.prod (hcoord a))
  have hc₀ : AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => -deriv preferredMovingBranch z.1) (s,q) :=
    (AnalyticAt.comp (f := fun z : ℂ × (Fin N → ℂ) => z.1)
      (g := deriv preferredMovingBranch) hB.deriv analyticAt_fst).neg
  have hE : AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) =>
      collectiveResidual (fun a => preferredSourceUDot z.1 (z.2 a))
        (fun a => preferredSourceUQ z.1 (z.2 a)) (-deriv preferredMovingBranch z.1)) (s,q) := by
    unfold collectiveResidual
    exact (Finset.univ.analyticAt_fun_sum (fun a _ => hd a)).neg.sub
      (hc₀.mul
        (Finset.univ.analyticAt_fun_sum (fun a _ => hv a)))
  have hDen : AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) =>
      collectiveDenominator (fun a => preferredMovingInverse z.1 (z.2 a))) (s,q) := by
    unfold collectiveDenominator
    exact (Finset.univ.analyticAt_fun_sum (fun a _ =>
      Finset.univ.analyticAt_fun_sum (fun b _ => ((hu a).sub (hu b)).pow 2))).div_const
  have hPair (a : Fin N) : AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) =>
      preferredCollectivePairDifference z.1 (z.2 i) (z.2 j) (z.2 a)) (s,q) :=
    AnalyticAt.comp
      (f := fun z : ℂ × (Fin N → ℂ) => (((z.1,z.2 a),z.2 j),z.2 i))
      (g := fun z : ((ℂ × ℂ) × ℂ) × ℂ => preferredCollectivePairDifference z.1.1.1 z.2 z.1.2 z.1.1.2)
      (preferredCollectivePairDifference_analyticAt s (q i) (q j) (q a) D c hc hD hU hcurv
        (hq i) (hq j) (hq a))
      (((analyticAt_fst.prod (hcoord a)).prod (hcoord j)).prod (hcoord i))
  exact (hE.fun_div hDen hR).mul (Finset.univ.analyticAt_fun_sum (fun a _ => hPair a))

end
end IsingBulk.Preferred22
