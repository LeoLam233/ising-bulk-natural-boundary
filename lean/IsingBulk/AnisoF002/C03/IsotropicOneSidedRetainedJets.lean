import IsingBulk.AnisoF002.C03.IsotropicOneSidedGaussian
import IsingBulk.AnisoF002.C03.IsotropicOneSidedImage

/-!
# Complete retained numerator jets on the actual whole one-sided image

The proved actual compact arc, physical complete pair, regular one-body
factor, and balanced homotopy are combined here. All fixed joint jets
have Gaussian decay on the same product neighborhood and on its actual
deformed images, including endpoint slivers. The constrained scalar
current and shell/coarea integrations remain separate obligations.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

theorem oneSidedSingle_of_thickening {S r : ℝ} {s a : ℂ}
    (hs : dist s (S : ℂ) < r) (ha : a ∈ thickening r (oneSidedCoordinateArc S)) :
    (s, a) ∈ thickening r (oneSidedParameterArc S) := by
  obtain ⟨a₀, ha₀, hda⟩ := mem_thickening_iff.mp ha
  apply mem_thickening_iff.mpr
  refine ⟨((S : ℂ), a₀), ⟨rfl, ha₀⟩, ?_⟩
  simpa only [Prod.dist_eq, max_lt_iff] using And.intro hs hda

theorem oneSidedProductDomain_mono (S : ℝ) {r₁ r₂ : ℝ} (h : r₁ ≤ r₂) (N : ℕ) :
    oneSidedProductDomain S r₁ N ⊆ oneSidedProductDomain S r₂ N :=
  fun _ hq => ⟨hq.1.trans_le h, fun i => thickening_mono h _ (hq.2 i)⟩

theorem oneSidedProductDomain_half_ball_subset (S r : ℝ) (N : ℕ)
    (q : ℂ × (Fin N → ℂ)) (hq : q ∈ oneSidedProductDomain S (r / 2) N) :
    ball q (r / 2) ⊆ oneSidedProductDomain S r N := by
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

theorem exists_oneSidedOneBody_protected_bound (S : ℝ) (hS : 0 < S ∧ S < 2) :
    ∃ r C : ℝ, 0 < r ∧ 0 < C ∧
      AnalyticOnNhd ℂ regularInverseOneBody (cthickening r (oneSidedParameterArc S)) ∧
      ∀ q ∈ cthickening r (oneSidedParameterArc S), ‖regularInverseOneBody q‖ ≤ C := by
  obtain ⟨r, hr, hU, hd, _⟩ :=
    exists_oneSided_inverse_protected_neighborhood S hS
  have hA : AnalyticOnNhd ℂ regularInverseOneBody (cthickening r (oneSidedParameterArc S)) := by
    intro q hq
    exact joint_regularOneBody_analyticAt explicitRightInverse q (hU q hq) (hd q hq).2.2
  obtain ⟨C₀, hC₀⟩ := (oneSidedParameterArc_isCompact S hS.1).cthickening.exists_bound_of_continuousOn
    hA.continuousOn
  exact ⟨r, max 1 C₀, hr, lt_of_lt_of_le zero_lt_one (le_max_left _ _), hA,
    fun q hq => (hC₀ q hq).trans (le_max_right _ _)⟩

/-- The actual complete retained numerator has one uniform Gaussian
bound and is jointly analytic on the same common product neighborhood. -/
theorem exists_actual_oneSided_retainedNumerator_analytic_gaussian (S : ℝ) (hS : 0 < S ∧ S < 2) :
    ∃ r κ C M : ℝ, 0 < r ∧ 0 < κ ∧ 0 < C ∧ 0 < M ∧
      ∀ (N : ℕ) (R : Finset (Fin N × Fin N)), R ⊆ indexPairs N →
      ∀ q ∈ oneSidedProductDomain S r N,
        AnalyticAt ℂ (retainedRegularNumerator R) q ∧
          ‖retainedRegularNumerator R q‖ ≤
            C ^ N * M ^ R.card * Real.exp (-κ * (N : ℝ) ^ 2 + (1 / 2 : ℝ) * N) := by
  obtain ⟨rG, κ, M, hrG, hκ, hM, hG⟩ := exists_actual_oneSided_retainedPair_gaussian S hS
  obtain ⟨rP, hrP, _, hP, hA, _, _⟩ := exists_oneSided_completePair_protected_neighborhood S hS
  obtain ⟨rU, C, hrU, hC, hU, hB⟩ := exists_oneSidedOneBody_protected_bound S hS
  let r := min rG (min rP rU)
  have hr : 0 < r := lt_min hrG (lt_min hrP hrU)
  have hrG' : r ≤ rG := min_le_left _ _
  have hrP' : r ≤ rP := (min_le_right _ _).trans (min_le_left _ _)
  have hrU' : r ≤ rU := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨r, κ, C, M, hr, hκ, hC, hM, ?_⟩
  intro N R hR q hq
  have hp : ∀ i j, (q.1, q.2 i, q.2 j) ∈ cthickening rP (oneSidedPairParameterArc S) :=
    fun i j => thickening_subset_cthickening_of_le hrP' _
      (oneSidedPair_of_thickening hq.1 (hq.2 i) (hq.2 j))
  have hu : ∀ i, (q.1, q.2 i) ∈ cthickening rU (oneSidedParameterArc S) :=
    fun i => thickening_subset_cthickening_of_le hrU' _
      (oneSidedSingle_of_thickening hq.1 (hq.2 i))
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
  have hqG := oneSidedProductDomain_mono S hrG' N hq
  have hpairbound := hG N R hR q.1 q.2 hqG.1 hqG.2
  refine ⟨hone.mul hret, ?_⟩
  rw [retainedRegularNumerator, norm_mul]
  exact (mul_le_mul honebound hpairbound (norm_nonneg _) (pow_nonneg hC.le _)).trans_eq
    (by ring)

/-- Every fixed total joint derivative has the same complete Gaussian
decay on one protected whole one-sided product neighborhood. The derivative
constant is independent of N and of the retained collision set.

Taking R to be the internal pairs of any fixed ell gives the retained
collision form required for the current iteration. -/
theorem exists_actual_oneSided_retainedNumerator_all_joint_jets (S : ℝ) (hS : 0 < S ∧ S < 2) :
    ∃ r κ C M : ℝ, 0 < r ∧ 0 < κ ∧ 0 < C ∧ 0 < M ∧
      ∀ k : ℕ, ∃ Ck : ℝ, 0 < Ck ∧
      ∀ (N : ℕ) (R : Finset (Fin N × Fin N)), R ⊆ indexPairs N →
      ∀ q ∈ oneSidedProductDomain S r N,
        ‖iteratedFDeriv ℂ k (retainedRegularNumerator R) q‖ ≤
          Ck * C ^ N * M ^ R.card * Real.exp (-κ * (N : ℝ) ^ 2 + (1 / 2 : ℝ) * N) := by
  obtain ⟨r₀, κ, C, M, hr₀, hκ, hC, hM, hall⟩ :=
    exists_actual_oneSided_retainedNumerator_analytic_gaussian S hS
  refine ⟨r₀ / 2, κ, C, M, half_pos hr₀, hκ, hC, hM, ?_⟩
  intro k
  refine ⟨protectedJetConstant k (r₀ / 2), protectedJetConstant_pos k (half_pos hr₀), ?_⟩
  intro N R hR q hq
  have hball := oneSidedProductDomain_half_ball_subset S r₀ N q hq
  have h := analytic_ball_joint_jet_bound k (retainedRegularNumerator R) q (r₀ / 2)
    (C ^ N * M ^ R.card * Real.exp (-κ * (N : ℝ) ^ 2 + (1 / 2 : ℝ) * N))
    (half_pos hr₀) (fun p hp => (hall N R hR p (hball hp)).1)
    (fun p hp => (hall N R hR p (hball hp)).2)
  simpa only [mul_assoc] using h


/-- Complete fixed joint jets on the actual balanced left/right image,
including both endpoint slivers, with all constants chosen before N. -/
theorem exists_actual_oneSided_homotopy_retained_jets (S : ℝ) (hS : 0 < S ∧ S < 2) :
    ∃ δ κ C M : ℝ, 0 < δ ∧ 0 < κ ∧ 0 < C ∧ 0 < M ∧
      ∀ k : ℕ, ∃ Ck : ℝ, 0 < Ck ∧
      ∀ (N : ℕ), 0 < N →
      ∀ (R : Finset (Fin N × Fin N)), R ⊆ indexPairs N →
      ∀ (s : ℂ), 0 < s.im → dist s (S : ℂ) < δ →
      ∀ (η τ ξ : ℝ), 0 < η → τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ θ : Fin N → ℝ, (∀ i, θ i ∈ Icc (-Real.pi - δ) δ) →
        ‖iteratedFDeriv ℂ k (retainedRegularNumerator R)
          (actualHomotopyRegularTuple s η τ ξ θ)‖ ≤
          Ck * C ^ N * M ^ R.card * Real.exp (-κ * (N : ℝ) ^ 2 + (1 / 2 : ℝ) * N) := by
  obtain ⟨r, κ, C, M, hr, hκ, hC, hM, hjets⟩ :=
    exists_actual_oneSided_retainedNumerator_all_joint_jets S hS
  obtain ⟨δ, hδ, hdomain⟩ := exists_actual_oneSided_homotopy_domain S r hS hr
  refine ⟨δ, κ, C, M, hδ, hκ, hC, hM, ?_⟩
  intro k
  obtain ⟨Ck, hCk, hk⟩ := hjets k
  refine ⟨Ck, hCk, ?_⟩
  intro N hN R hR s hs hsnear η τ ξ hη hτ hξ θ hθ
  exact hk N R hR _ (hdomain N hN s hs hsnear η τ ξ hη hτ hξ θ hθ).1

end IsingBulk.AnisoF002.Isotropic
