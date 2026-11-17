import IsingBulk.AnisoF002.C03.IsotropicRetainedGaussian
import IsingBulk.AnisoF002.C03.IsotropicUniformJets

/-!
# Complete retained numerators: one common domain and every joint jet

The one-body factors and every pair are the actual regular-coordinate
expressions. The common neighborhood, Gaussian constant, and per-body
and per-retained-pair constants precede N. All fixed joint Fréchet jets
then follow from a dimension-independent analytic ball estimate.

This is the right-neighborhood numerator part of the frozen cell Gaussian
lemma. Actual deformed-image inclusion, the left arc, scalar current,
coarea, and the complete particle tail are not asserted by this file.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

def rightProductDomain (S r : ℝ) (N : ℕ) : Set (ℂ × (Fin N → ℂ)) :=
  {q | dist q.1 (S : ℂ) < r ∧ ∀ i, q.2 i ∈ thickening r (rightCoordinateInterval S)}

theorem rightSingle_of_thickening {S r : ℝ} {s a : ℂ}
    (hs : dist s (S : ℂ) < r) (ha : a ∈ thickening r (rightCoordinateInterval S)) :
    (s, a) ∈ thickening r (rightParameterSegment S) := by
  obtain ⟨a₀, ha₀, hda⟩ := mem_thickening_iff.mp ha
  apply mem_thickening_iff.mpr
  refine ⟨((S : ℂ), a₀), ⟨rfl, ha₀⟩, ?_⟩
  simpa only [Prod.dist_eq, max_lt_iff] using And.intro hs hda

theorem rightProductDomain_mono (S : ℝ) {r₁ r₂ : ℝ} (h : r₁ ≤ r₂) (N : ℕ) :
    rightProductDomain S r₁ N ⊆ rightProductDomain S r₂ N :=
  fun _ hq => ⟨hq.1.trans_le h, fun i => thickening_mono h _ (hq.2 i)⟩

theorem rightProductDomain_half_ball_subset (S r : ℝ) (N : ℕ)
    (q : ℂ × (Fin N → ℂ)) (hq : q ∈ rightProductDomain S (r / 2) N) :
    ball q (r / 2) ⊆ rightProductDomain S r N := by
  intro p hp
  have hdist : dist p.1 q.1 < r / 2 ∧ dist p.2 q.2 < r / 2 := by
    simpa only [mem_ball, Prod.dist_eq, max_lt_iff] using hp
  refine ⟨(dist_triangle p.1 q.1 (S : ℂ)).trans_lt (by linarith [hq.1, hdist.1]), ?_⟩
  intro i
  obtain ⟨a, ha, hqa⟩ := mem_thickening_iff.mp (hq.2 i)
  apply mem_thickening_iff.mpr
  refine ⟨a, ha, (dist_triangle (p.2 i) (q.2 i) a).trans_lt ?_⟩
  have hi := (dist_le_pi_dist p.2 q.2 i).trans_lt hdist.2
  linarith

theorem exists_rightOneBody_protected_bound (S : ℝ) (hS : 0 < S ∧ S < 2) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
      AnalyticOnNhd ℂ regularInverseOneBody (cthickening r (rightParameterSegment S)) ∧
      ∀ q ∈ cthickening r (rightParameterSegment S), ‖regularInverseOneBody q‖ ≤ C := by
  obtain ⟨r, _, hr, _, _, _, hU, hd, _⟩ :=
    exists_right_inverse_common_convex_neighborhood S hS
  have hA : AnalyticOnNhd ℂ regularInverseOneBody (cthickening r (rightParameterSegment S)) := by
    intro q hq
    exact joint_regularOneBody_analyticAt explicitRightInverse q (hU q hq) (hd q hq).2.1
  obtain ⟨C₀, hC₀⟩ := (rightParameterSegment_isCompact S).cthickening.exists_bound_of_continuousOn
    hA.continuousOn
  exact ⟨r, max 1 C₀, hr, lt_of_lt_of_le zero_lt_one (le_max_left _ _), hA,
    fun q hq => (hC₀ q hq).trans (le_max_right _ _)⟩

/-- The actual complete retained numerator has one uniform Gaussian
bound and is jointly analytic on the same common product neighborhood. -/
theorem exists_actual_retainedNumerator_analytic_gaussian (S : ℝ) (hS : 0 < S ∧ S < 2) :
    ∃ r κ C M : ℝ, 0 < r ∧ 0 < κ ∧ 0 < C ∧ 0 < M ∧
      ∀ (N : ℕ) (R : Finset (Fin N × Fin N)), R ⊆ indexPairs N →
      ∀ q ∈ rightProductDomain S r N,
        AnalyticAt ℂ (retainedRegularNumerator R) q ∧
          ‖retainedRegularNumerator R q‖ ≤
            C ^ N * M ^ R.card * Real.exp (-κ * (N : ℝ) ^ 2 + (1 / 2 : ℝ) * N) := by
  obtain ⟨rG, κ, M, hrG, hκ, hM, hG⟩ := exists_actual_right_retainedPair_gaussian S hS
  obtain ⟨rP, hrP, _, hP, hA, _, _⟩ := exists_right_completePair_protected_neighborhood S hS
  obtain ⟨rU, C, hrU, hC, hU, hB⟩ := exists_rightOneBody_protected_bound S hS
  let r := min rG (min rP rU)
  have hr : 0 < r := lt_min hrG (lt_min hrP hrU)
  have hrG' : r ≤ rG := min_le_left _ _
  have hrP' : r ≤ rP := (min_le_right _ _).trans (min_le_left _ _)
  have hrU' : r ≤ rU := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨r, κ, C, M, hr, hκ, hC, hM, ?_⟩
  intro N R hR q hq
  have hp : ∀ i j, (q.1, q.2 i, q.2 j) ∈ cthickening rP (rightPairParameterSegment S) :=
    fun i j => thickening_subset_cthickening_of_le hrP' _
      (rightPair_of_thickening hq.1 (hq.2 i) (hq.2 j))
  have hu : ∀ i, (q.1, q.2 i) ∈ cthickening rU (rightParameterSegment S) :=
    fun i => thickening_subset_cthickening_of_le hrU' _
      (rightSingle_of_thickening hq.1 (hq.2 i))
  have hret := retainedInversePairProduct_analyticAt R q
    (fun ij _ => hA _ (hp ij.1 ij.2)) (fun ij _ => hP _ (hp ij.1 ij.2))
  have hone : AnalyticAt ℂ
      (fun p : ℂ × (Fin N → ℂ) => ∏ i, regularInverseOneBody (p.1, p.2 i)) q := by
    apply Finset.analyticAt_fun_prod
    intro i _
    exact (hU _ (hu i)).comp (f := fun p : ℂ × (Fin N → ℂ) => (p.1, p.2 i))
      (analyticAt_fst.prod (coordinate_analyticAt q i))
  have honebound : ‖∏ i, regularInverseOneBody (q.1, q.2 i)‖ ≤ C ^ N := by
    rw [norm_prod]
    calc
      _ ≤ ∏ _i : Fin N, C := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        (fun i _ => hB _ (hu i))
      _ = C ^ N := by simp
  have hqG := rightProductDomain_mono S hrG' N hq
  have hpairbound := hG N R hR q.1 q.2 hqG.1 hqG.2
  refine ⟨hone.mul hret, ?_⟩
  rw [retainedRegularNumerator, norm_mul]
  exact (mul_le_mul honebound hpairbound (norm_nonneg _) (pow_nonneg hC.le _)).trans_eq
    (by ring)

/-- Every fixed total joint derivative has the same complete Gaussian
decay on one protected right product neighborhood. The derivative
constant is independent of N and of the retained collision set.

Taking R to be the internal pairs of any fixed ell gives the retained
collision form required for the right current iteration. -/
theorem exists_actual_retainedNumerator_all_joint_jets (S : ℝ) (hS : 0 < S ∧ S < 2) :
    ∃ r κ C M : ℝ, 0 < r ∧ 0 < κ ∧ 0 < C ∧ 0 < M ∧
      ∀ k : ℕ, ∃ Ck : ℝ, 0 < Ck ∧
      ∀ (N : ℕ) (R : Finset (Fin N × Fin N)), R ⊆ indexPairs N →
      ∀ q ∈ rightProductDomain S r N,
        ‖iteratedFDeriv ℂ k (retainedRegularNumerator R) q‖ ≤
          Ck * C ^ N * M ^ R.card * Real.exp (-κ * (N : ℝ) ^ 2 + (1 / 2 : ℝ) * N) := by
  obtain ⟨r₀, κ, C, M, hr₀, hκ, hC, hM, hall⟩ :=
    exists_actual_retainedNumerator_analytic_gaussian S hS
  refine ⟨r₀ / 2, κ, C, M, half_pos hr₀, hκ, hC, hM, ?_⟩
  intro k
  refine ⟨protectedJetConstant k (r₀ / 2), protectedJetConstant_pos k (half_pos hr₀), ?_⟩
  intro N R hR q hq
  have hball := rightProductDomain_half_ball_subset S r₀ N q hq
  have h := analytic_ball_joint_jet_bound k (retainedRegularNumerator R) q (r₀ / 2)
    (C ^ N * M ^ R.card * Real.exp (-κ * (N : ℝ) ^ 2 + (1 / 2 : ℝ) * N))
    (half_pos hr₀) (fun p hp => (hall N R hR p (hball hp)).1)
    (fun p hp => (hall N R hR p (hball hp)).2)
  simpa only [mul_assoc] using h

end IsingBulk.AnisoF002.Isotropic
