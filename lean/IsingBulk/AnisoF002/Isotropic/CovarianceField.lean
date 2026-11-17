import IsingBulk.AnisoF002.Isotropic.BalancedContour

/-!
# F002: exact covariance transport identities

This is the algebra of `eq:iso-covariance-field`, for the filled analytic
secants.  It establishes both transport constraints without dividing by
any individual coordinate difference.  Proving the analytic inverse,
its secants, and their uniform bounds remains separate.
-/
noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- The unordered-pair quadratic variance, expressed without an index order. -/
def pairVariance (U : ι → ℂ) : ℂ :=
  (1 / 2 : ℂ) * ∑ i, ∑ j, (U i - U j) ^ 2

/-- Filled pair field: only the analytic nonzero second secant is divided out. -/
def secantPair (v : ι → ℂ) (dU dV : ι → ι → ℂ) (i j : ι) : ℂ :=
  (v i - v j) * (dU i j) ^ 2 / dV i j

omit [Fintype ι] in
theorem secantPair_antisymm (v : ι → ℂ) (dU dV : ι → ι → ℂ)
    (hu : ∀ i j, dU j i = dU i j) (hv : ∀ i j, dV j i = dV i j)
    (i j : ι) : secantPair v dU dV j i = -secantPair v dU dV i j := by
  unfold secantPair
  rw [hu i j, hv i j]
  ring

omit [Fintype ι] in
theorem secantPair_diagonal (v : ι → ℂ) (dU dV : ι → ι → ℂ) (i : ι) :
    secantPair v dU dV i i = 0 := by
  simp [secantPair]

omit [Fintype ι] in
/-- The pair contraction is valid also at coincident coordinates. -/
theorem secantPair_contract (v U V : ι → ℂ) (dU dV : ι → ι → ℂ)
    (hU : ∀ i j, U i - U j = (v i - v j) * dU i j)
    (hV : ∀ i j, V i - V j = (v i - v j) * dV i j)
    (hE : ∀ i j, dV i j ≠ 0) (i j : ι) :
    (V i - V j) * secantPair v dU dV i j = (U i - U j) ^ 2 := by
  rw [hU i j, hV i j]
  unfold secantPair
  field_simp [hE i j]

/-- A double antisymmetric sum vanishes by transposition. -/
theorem sum_antisymmetric (H : ι → ι → ℂ)
    (hH : ∀ i j, H j i = -H i j) : (∑ i, ∑ j, H i j) = 0 := by
  have h : (∑ i, ∑ j, H i j) = -(∑ i, ∑ j, H i j) := by
    calc
      (∑ i, ∑ j, H i j) = ∑ j, ∑ i, H i j := Finset.sum_comm
      _ = ∑ j, ∑ i, -H j i := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        exact hH j i
      _ = -(∑ i, ∑ j, H i j) := by simp only [Finset.sum_neg_distrib]
  linear_combination (1 / 2 : ℂ) * h

/-- Antisymmetry turns the weighted double sum into the complete variance. -/
theorem weighted_sum_antisymmetric (U V : ι → ℂ) (H : ι → ι → ℂ)
    (hH : ∀ i j, H j i = -H i j)
    (hcontract : ∀ i j, (V i - V j) * H i j = (U i - U j) ^ 2) :
    (∑ i, V i * (∑ j, H i j)) = pairVariance U := by
  have hswap : (∑ i, ∑ j, V j * H i j) =
      -(∑ i, ∑ j, V i * H i j) := by
    calc
      (∑ i, ∑ j, V j * H i j) = ∑ j, ∑ i, V j * H i j := Finset.sum_comm
      _ = ∑ j, ∑ i, -(V j * H j i) := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        rw [hH j i]
        ring
      _ = -(∑ i, ∑ j, V i * H i j) := by simp only [Finset.sum_neg_distrib]
  have hdiff : (∑ i, ∑ j, (U i - U j) ^ 2) =
      2 * (∑ i, ∑ j, V i * H i j) := by
    calc
      (∑ i, ∑ j, (U i - U j) ^ 2) = ∑ i, ∑ j, (V i - V j) * H i j := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact (hcontract i j).symm
      _ = (∑ i, ∑ j, V i * H i j) - (∑ i, ∑ j, V j * H i j) := by
        simp only [sub_mul, Finset.sum_sub_distrib]
      _ = 2 * (∑ i, ∑ j, V i * H i j) := by rw [hswap]; ring
  calc
    (∑ i, V i * (∑ j, H i j)) = ∑ i, ∑ j, V i * H i j := by
      simp only [Finset.mul_sum]
    _ = pairVariance U := by
      unfold pairVariance
      rw [hdiff]
      ring

/-- Actual normalized covariance field. -/
def covarianceField (A : ℂ) (U : ι → ℂ) (H : ι → ι → ℂ) (i : ι) : ℂ :=
  A * (∑ j, H i j) / pairVariance U

theorem covarianceField_sum (A : ℂ) (U : ι → ℂ) (H : ι → ι → ℂ)
    (hH : ∀ i j, H j i = -H i j) :
    ∑ i, covarianceField A U H i = 0 := by
  simp only [covarianceField, ← Finset.sum_div, ← Finset.mul_sum]
  rw [sum_antisymmetric H hH]
  simp

theorem covarianceField_weighted (A : ℂ) (U V : ι → ℂ) (H : ι → ι → ℂ)
    (hH : ∀ i j, H j i = -H i j)
    (hcontract : ∀ i j, (V i - V j) * H i j = (U i - U j) ^ 2)
    (hD : pairVariance U ≠ 0) :
    (∑ i, V i * covarianceField A U H i) = A := by
  calc
    (∑ i, V i * covarianceField A U H i) =
        A * (∑ i, V i * (∑ j, H i j)) / pairVariance U := by
      calc
        (∑ i, V i * covarianceField A U H i) =
            ∑ i, (A * (V i * (∑ j, H i j))) / pairVariance U := by
          apply Finset.sum_congr rfl
          intro i _
          unfold covarianceField
          ring
        _ = A * (∑ i, V i * (∑ j, H i j)) / pairVariance U := by
          rw [← Finset.sum_div, ← Finset.mul_sum]
    _ = A := by rw [weighted_sum_antisymmetric U V H hH hcontract]; exact mul_div_cancel_right₀ A hD

end IsingBulk.AnisoF002.Isotropic
