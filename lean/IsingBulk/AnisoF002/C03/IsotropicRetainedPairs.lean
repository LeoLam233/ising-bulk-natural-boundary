import IsingBulk.AnisoF002.C03.IsotropicProtectedPair
import IsingBulk.AnisoF002.C03.IsotropicAnalyticCovariance

/-!
# Complete finite products with explicitly retained collision factors

Every pair is retained in the complete product. Any selected finite set
of collision squares can be factored while the remaining quotient stays
jointly analytic, also at partial and total coincidences. The quotient is
constructed from the proved complete-pair factorization, not by pointwise
division on a diagonal. Gaussian estimates and actual contour inclusion
are separate obligations.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

def completeInversePairProduct (N : ℕ) (q : ℂ × (Fin N → ℂ)) : ℂ :=
  ∏ ij ∈ indexPairs N, inversePairFilled explicitRightInverse (q.1, q.2 ij.1, q.2 ij.2)

def retainedCollisionPolynomial {N : ℕ} (R : Finset (Fin N × Fin N))
    (v : Fin N → ℂ) : ℂ :=
  ∏ ij ∈ R, (v ij.1 - v ij.2) ^ 2

def retainedInversePairProduct {N : ℕ} (R : Finset (Fin N × Fin N))
    (q : ℂ × (Fin N → ℂ)) : ℂ :=
  (∏ ij ∈ R, inversePairCollisionCoefficient explicitRightInverse (q.1, q.2 ij.1, q.2 ij.2)) *
    ∏ ij ∈ indexPairs N \ R,
      inversePairFilled explicitRightInverse (q.1, q.2 ij.1, q.2 ij.2)

def regularInverseOneBody (q : ℂ × ℂ) : ℂ :=
  regularOneBody (explicitRightInverse q) (q.2 - explicitRightInverse q)

def completeRegularNumerator (N : ℕ) (q : ℂ × (Fin N → ℂ)) : ℂ :=
  (∏ i, regularInverseOneBody (q.1, q.2 i)) * completeInversePairProduct N q

def retainedRegularNumerator {N : ℕ} (R : Finset (Fin N × Fin N))
    (q : ℂ × (Fin N → ℂ)) : ℂ :=
  (∏ i, regularInverseOneBody (q.1, q.2 i)) * retainedInversePairProduct R q

theorem completeInversePairProduct_factorization {N : ℕ}
    (R : Finset (Fin N × Fin N)) (hR : R ⊆ indexPairs N) (q : ℂ × (Fin N → ℂ))
    (hfactor : ∀ ij ∈ R,
      inversePairFilled explicitRightInverse (q.1, q.2 ij.1, q.2 ij.2) =
        (q.2 ij.1 - q.2 ij.2) ^ 2 *
          inversePairCollisionCoefficient explicitRightInverse (q.1, q.2 ij.1, q.2 ij.2)) :
    completeInversePairProduct N q =
      retainedCollisionPolynomial R q.2 * retainedInversePairProduct R q := by
  unfold completeInversePairProduct retainedCollisionPolynomial retainedInversePairProduct
  rw [← Finset.prod_sdiff hR]
  have hprod := Finset.prod_congr rfl hfactor
  rw [hprod, Finset.prod_mul_distrib]
  ring

theorem completeRegularNumerator_factorization {N : ℕ}
    (R : Finset (Fin N × Fin N)) (hR : R ⊆ indexPairs N) (q : ℂ × (Fin N → ℂ))
    (hfactor : ∀ ij ∈ R,
      inversePairFilled explicitRightInverse (q.1, q.2 ij.1, q.2 ij.2) =
        (q.2 ij.1 - q.2 ij.2) ^ 2 *
          inversePairCollisionCoefficient explicitRightInverse (q.1, q.2 ij.1, q.2 ij.2)) :
    completeRegularNumerator N q =
      retainedCollisionPolynomial R q.2 * retainedRegularNumerator R q := by
  unfold completeRegularNumerator retainedRegularNumerator
  rw [completeInversePairProduct_factorization R hR q hfactor]
  ring

theorem retainedInversePairProduct_eq_quotient {N : ℕ}
    (R : Finset (Fin N × Fin N)) (hR : R ⊆ indexPairs N) (q : ℂ × (Fin N → ℂ))
    (hfactor : ∀ ij ∈ R,
      inversePairFilled explicitRightInverse (q.1, q.2 ij.1, q.2 ij.2) =
        (q.2 ij.1 - q.2 ij.2) ^ 2 *
          inversePairCollisionCoefficient explicitRightInverse (q.1, q.2 ij.1, q.2 ij.2))
    (hne : retainedCollisionPolynomial R q.2 ≠ 0) :
    completeInversePairProduct N q / retainedCollisionPolynomial R q.2 =
      retainedInversePairProduct R q := by
  rw [completeInversePairProduct_factorization R hR q hfactor]
  exact mul_div_cancel_left₀ _ hne

theorem retainedInversePairProduct_analyticAt {N : ℕ}
    (R : Finset (Fin N × Fin N)) (q : ℂ × (Fin N → ℂ))
    (hcoeff : ∀ ij ∈ R, AnalyticAt ℂ (inversePairCollisionCoefficient explicitRightInverse)
      (q.1, q.2 ij.1, q.2 ij.2))
    (hpair : ∀ ij ∈ indexPairs N \ R, AnalyticAt ℂ (inversePairFilled explicitRightInverse)
      (q.1, q.2 ij.1, q.2 ij.2)) :
    AnalyticAt ℂ (retainedInversePairProduct R) q := by
  have hmap (i j : Fin N) : AnalyticAt ℂ
      (fun p : ℂ × (Fin N → ℂ) => (p.1, p.2 i, p.2 j)) q :=
    analyticAt_fst.prod ((coordinate_analyticAt q i).prod (coordinate_analyticAt q j))
  exact (Finset.analyticAt_fun_prod R (fun ij hij => (hcoeff ij hij).comp
    (f := fun p : ℂ × (Fin N → ℂ) => (p.1, p.2 ij.1, p.2 ij.2)) (hmap ij.1 ij.2))).mul
    (Finset.analyticAt_fun_prod (indexPairs N \ R) (fun ij hij => (hpair ij hij).comp
      (f := fun p : ℂ × (Fin N → ℂ) => (p.1, p.2 ij.1, p.2 ij.2)) (hmap ij.1 ij.2)))

/-- The common protected pair neighborhood precedes every N and every
retained collision set. Every actual complete pair stays in the formula. -/
theorem exists_common_retainedPair_neighborhood (S : ℝ) (hS : 0 < S ∧ S < 2) :
    ∃ r : ℝ, 0 < r ∧
      rightPairParameterSegment S ⊆ thickening r (rightPairParameterSegment S) ∧
      ∀ (N : ℕ) (R : Finset (Fin N × Fin N)), R ⊆ indexPairs N →
        ∀ q : ℂ × (Fin N → ℂ),
        (∀ ij ∈ indexPairs N,
          (q.1, q.2 ij.1, q.2 ij.2) ∈ cthickening r (rightPairParameterSegment S)) →
        AnalyticAt ℂ (retainedInversePairProduct R) q ∧
          completeInversePairProduct N q =
            retainedCollisionPolynomial R q.2 * retainedInversePairProduct R q := by
  obtain ⟨r, hr, hsub, hp, ha, hf, _⟩ := exists_right_completePair_protected_neighborhood S hS
  refine ⟨r, hr, hsub, ?_⟩
  intro N R hR q hq
  refine ⟨retainedInversePairProduct_analyticAt R q
    (fun ij hij => ha _ (hq ij (hR hij)))
    (fun ij hij => hp _ (hq ij (Finset.mem_sdiff.mp hij).1)), ?_⟩
  exact completeInversePairProduct_factorization R hR q
    (fun ij hij => hf _ (hq ij (hR hij)))

/-- On the actual real right tuple the regular one-body factors and all
complete pairs admit a jointly analytic retained-collision quotient.
No noncoincidence assumption is required. -/
theorem retainedRegularNumerator_real_right (S : ℝ) (hS : 0 < S ∧ S < 2)
    (N : ℕ) (R : Finset (Fin N × Fin N)) (hR : R ⊆ indexPairs N)
    (w : Fin N → ℝ) (hw : ∀ i, w i ∈ Icc (-rightBranchEndpoint S) 0) :
    let v : Fin N → ℂ := fun i => (rightArcCoordinate S (w i) : ℂ)
    AnalyticAt ℂ (retainedRegularNumerator R) ((S : ℂ), v) ∧
      completeRegularNumerator N ((S : ℂ), v) =
        retainedCollisionPolynomial R v * retainedRegularNumerator R ((S : ℂ), v) := by
  dsimp only
  let v : Fin N → ℂ := fun i => (rightArcCoordinate S (w i) : ℂ)
  have hv : ∀ i, v i ∈ Complex.ofReal '' Icc (-rightBranchEndpoint S) (rightBranchEndpoint S) := by
    intro i
    refine ⟨rightArcCoordinate S (w i), ?_, rfl⟩
    rw [← rightArcCoordinate_image S hS]
    exact ⟨w i, hw i, rfl⟩
  have hmem : ∀ i j, ((S : ℂ), v i, v j) ∈ rightPairParameterSegment S :=
    fun i j => ⟨rfl, hv i, hv j⟩
  obtain ⟨r, _, _, hp, ha, hf, _⟩ := exists_right_completePair_protected_neighborhood S hS
  have hret := retainedInversePairProduct_analyticAt R ((S : ℂ), v)
    (fun ij _ => ha _ (self_subset_cthickening _ (hmem ij.1 ij.2)))
    (fun ij _ => hp _ (self_subset_cthickening _ (hmem ij.1 ij.2)))
  have hone : AnalyticAt ℂ
      (fun p : ℂ × (Fin N → ℂ) => ∏ i, regularInverseOneBody (p.1, p.2 i)) ((S : ℂ), v) := by
    apply Finset.analyticAt_fun_prod
    intro i _
    have hd := explicitRightInverse_data_on_arc S (w i) hS (hw i)
    exact (joint_regularOneBody_analyticAt explicitRightInverse ((S : ℂ), v i) hd.1 hd.2.2.1).comp
      (f := fun p : ℂ × (Fin N → ℂ) => (p.1, p.2 i))
      (analyticAt_fst.prod (coordinate_analyticAt ((S : ℂ), v) i))
  exact ⟨hone.mul hret, completeRegularNumerator_factorization R hR ((S : ℂ), v)
    (fun ij _ => hf _ (self_subset_cthickening _ (hmem ij.1 ij.2)))⟩

end IsingBulk.AnisoF002.Isotropic
