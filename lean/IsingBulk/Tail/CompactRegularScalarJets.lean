import IsingBulk.Tail.CompactScalarPullbackJets
import IsingBulk.Tail.MixedAmplitudeScalarJets

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter
open scoped Topology ContDiff BigOperators
attribute [local fun_prop] analyticAt_fst analyticAt_snd
set_option maxHeartbeats 1800000

def compactPairQuotient (p : ℂ × ℂ × ℂ) : ℂ :=
  -selectedContinuedRoot p.1 p.2.1*selectedContinuedRoot p.1 p.2.2/
    (p.2.1*p.2.2*(1-selectedContinuedRoot p.1 p.2.1*selectedContinuedRoot p.1 p.2.2)^2)

theorem mixedCompactPair_factorization (p : ℂ × ℂ × ℂ) :
    mixedCompactPair p=(p.2.1-p.2.2)^2*compactPairQuotient p := by
  unfold mixedCompactPair compactPairQuotient canceledPair
  ring

theorem compactPairQuotient_analyticAt {s y v : ℂ}
    (hy : (s,y) ∈ mixedRootPairDomain) (hv : (s,v) ∈ mixedRootPairDomain) :
    AnalyticAt ℂ compactPairQuotient (s,y,v) := by
  have hzy : AnalyticAt ℂ (fun p : ℂ × ℂ × ℂ => selectedContinuedRoot p.1 p.2.1) (s,y,v) :=
    AnalyticAt.comp_of_eq (g := fun p : ℂ × ℂ => selectedContinuedRoot p.1 p.2)
      (f := fun p : ℂ × ℂ × ℂ => (p.1,p.2.1))
      (selectedContinuedRoot_joint_analyticAt hy.1 hy.2.1 hy.2.2) (by fun_prop) rfl
  have hzv : AnalyticAt ℂ (fun p : ℂ × ℂ × ℂ => selectedContinuedRoot p.1 p.2.2) (s,y,v) :=
    AnalyticAt.comp_of_eq (g := fun p : ℂ × ℂ => selectedContinuedRoot p.1 p.2)
      (f := fun p : ℂ × ℂ × ℂ => (p.1,p.2.2))
      (selectedContinuedRoot_joint_analyticAt hv.1 hv.2.1 hv.2.2) (by fun_prop) rfl
  unfold compactPairQuotient
  exact (hzy.neg.mul hzv).div (by fun_prop)
    (mul_ne_zero (mul_ne_zero hy.2.1 hv.2.1) (pow_ne_zero 2 (continuedRoot_pair_gap hy.2.2 hv.2.2)))

def compactRegularScalar (l : Bool ⊕ Fin 3) (p : ℂ × ℂ × ℂ) : ℂ :=
  match l with
  | Sum.inl false => compactPairQuotient p
  | Sum.inl true => mixedCompactPair p
  | Sum.inr a => mixedCompactAmplitudeFactor a p.1 p.2.1

theorem compact_right_base_pair_domain (d : LocalBranchData) {θ : ℝ}
    (hθ : |1+Real.cos d.thetaB-Real.cos θ| < 1) :
    (radialParameter d.theta 0,limitingAngle θ) ∈ mixedRootPairDomain := by
  refine ⟨norm_ne_zero_iff.mp (by simp [radialParameter_norm]),
    norm_ne_zero_iff.mp (by rw [limitingAngle_norm]; norm_num),?_⟩
  change sourceW (radialParameter d.theta 0) (limitingAngle θ) ∈ continuedRootDomain
  rw [sourceW_limitingAngle]
  exact Or.inr (by change |limitingAngularW d.thetaB θ| < 1; exact hθ)

theorem compactRegularScalar_base_analytic (d : LocalBranchData) {a b : ℝ}
    (hmargin : ∀ θ ∈ Icc a b, |1+Real.cos d.thetaB-Real.cos θ| < 1)
    (l : Bool ⊕ Fin 3) (θ : ℝ) (hθ : θ ∈ Icc a b) (φ : ℝ) (hφ : φ ∈ Icc a b) :
    AnalyticAt ℂ (compactRegularScalar l)
      (radialParameter d.theta 0,limitingAngle θ,limitingAngle φ) := by
  have hy := compact_right_base_pair_domain d (hmargin θ hθ)
  have hv := compact_right_base_pair_domain d (hmargin φ hφ)
  cases l with
  | inl l =>
    cases l with
    | false => exact compactPairQuotient_analyticAt hy hv
    | true =>
      exact mixedCompactPair_analyticAt hy.1 hy.2.1 hv.2.1 hy.2.2 hv.2.2
        (continuedRoot_pair_gap hy.2.2 hv.2.2)
  | inr a =>
    exact AnalyticAt.comp_of_eq (g := fun p : ℂ × ℂ => mixedCompactAmplitudeFactor a p.1 p.2)
      (f := fun p : ℂ × ℂ × ℂ => (p.1,p.2.1))
      (mixedCompactAmplitudeFactor_analyticAt a hy) (by fun_prop) rfl

theorem actual_compact_regular_scalar_jets (d : LocalBranchData) (f : SelectorFunctions)
    (hf : RegularSelector f) (hp1 : ∀ x, f.p x ≤ 1) {a b : ℝ}
    (hmargin : ∀ θ ∈ Icc a b, |1+Real.cos d.thetaB-Real.cos θ| < 1)
    (J : ℕ) : ∃ δ C : ℝ, 0 < δ ∧ 1 ≤ C ∧
      ∀ N : ℕ, 0 < N → ∀ eps τ lam : ℝ, 0 ≤ eps → 0 ≤ τ → τ ≤ 1 →
      0 ≤ lam → lam ≤ 1 → ∀ s : ℂ,
      ‖s-radialParameter d.theta 0‖+d.c₀*eps+2*lam ≤ δ →
      ∀ θ : Fin N → ℝ, ∀ i j : Fin N, θ i ∈ Icc a b → θ j ∈ Icc a b →
      ∀ l : Bool ⊕ Fin 3, RealScaledJetBound (fun q : ℂ × (Fin N → ℝ) =>
        compactRegularScalar l (q.1,deformedPoint f (Real.exp (-d.c₀*eps)) τ lam q.2 i,
          deformedPoint f (Real.exp (-d.c₀*eps)) τ lam q.2 j)) (s,θ) J 1 C 0 := by
  have hfamily (l : Bool ⊕ Fin 3) := actual_compact_scalar_pair_jets d f hf hp1
    (compactRegularScalar l) (compactRegularScalar_base_analytic d hmargin l) J
  choose δ C hδ hC hjets using hfamily
  let r := Finset.univ.inf' Finset.univ_nonempty δ
  let B := 1+∑ l,C l
  have hr : 0 < r := (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun l _ => hδ l)
  have hB : 1 ≤ B := by dsimp [B]; linarith [Finset.sum_nonneg (fun l (_ : l ∈ Finset.univ) => (hC l).le)]
  have hCB (l : Bool ⊕ Fin 3) : C l ≤ B := by
    have hh := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => (hC j).le) (Finset.mem_univ l)
    dsimp [B]
    linarith
  refine ⟨r,B,hr,hB,?_⟩
  intro N hN eps τ lam heps hτ hτ1 hlam hlam1 s hsmall θ i j hi hj l
  exact (hjets l N hN eps τ lam heps hτ hτ1 hlam hlam1 s
    (hsmall.trans (Finset.inf'_le _ (Finset.mem_univ l))) θ i j hi hj).mono zero_lt_one le_rfl (hCB l)

end
end IsingBulk.Tail
