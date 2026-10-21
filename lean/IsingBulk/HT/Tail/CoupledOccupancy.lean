import IsingBulk.Tail.CoupledOccupancyJets
import IsingBulk.Tail.ChangedPairProductJets

/-!
# HT coupled occupancy, without freezing the occupancy

The normalized occupancy and the rank-one Jacobian in HT-1.0 are literally
the LT definitions.  Their finite-jet theorems quantify over every positive
dimension, so no parity hypothesis is required.  These adapters record that
fact and retain the off-diagonal contraction explicitly.  They do not assert
that the complete differentiated HT contour has already been estimated.
-/

namespace IsingBulk.HT.Tail
noncomputable section
open scoped BigOperators ContDiff
open IsingBulk.Tail

/-- The action of a diagonal plus rank-one Jacobian.  In particular, the
second term is not discarded when a two-coordinate field is contracted
against the coupled angular Jacobian. -/
theorem diagonal_rankOne_action {N : ℕ} (d u v V : Fin N → ℂ) (i : Fin N) :
    (∑ j, ((if i = j then d i else 0) + u i * v j) * V j) =
      d i * V i + u i * ∑ j, v j * V j := by
  simp only [add_mul, Finset.sum_add_distrib]
  congr 1
  · simp
  · simp only [Finset.mul_sum, mul_assoc]

/-- Exactly the coupled contour Jacobian used in the frozen HT manuscript.
The final term moves every `m`-supported coordinate; it need not vanish. -/
theorem coupled_angular_action {N : ℕ} (lam tau : ℝ)
    (p m p' m' : Fin N → ℝ) (V : Fin N → ℂ) (i : Fin N) :
    (∑ j, retractionJacobian lam tau p m p' m' i j * V j) =
      (Complex.I + (lam * (-2 * tau * p' i +
        tau * occupancy p / (2 * N) * m' i) : ℝ)) * V i +
      (lam * tau / (2 * N) * m i : ℝ) * ∑ j, (p' j : ℂ) * V j := by
  simpa only [retractionJacobian, Complex.ofReal_mul] using diagonal_rankOne_action
    (fun i => Complex.I + (lam * (-2 * tau * p' i +
      tau * occupancy p / (2 * N) * m' i) : ℝ))
    (fun i => (lam * tau / (2 * N) * m i : ℝ))
    (fun j => (p' j : ℂ)) V i

/-- One constant works for every positive particle number and every
derivative order through the fixed ceiling.  In particular the constant
is selected before arbitrarily large odd `N`. -/
theorem coupled_occupancy_finite_jets (b eta alpha : ℝ) (k : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ N : ℕ, 0 < N → ∀ theta : Fin N → ℝ, ∀ j ≤ k,
      ‖iteratedFDeriv ℝ j (fun x : Fin N → ℝ =>
        occupancy (fun i => (constructedSelector b eta alpha).p (x i)) / (N : ℝ))
          theta‖ ≤ B :=
  IsingBulk.Tail.constructed_normalized_occupancy_finite_jets b eta alpha k

/-- The full determinant cost also precedes the particle-number
quantifier and is uniform in the closed homotopy parameter interval. -/
theorem coupled_jacobian_bound (b eta alpha tau : ℝ)
    (hb : 0 < Real.sin b) (heta : 0 < eta)
    (hetaSmall : eta ≤ Real.sin b / 4) (halpha : 0 < alpha) (htau : 0 ≤ tau) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N → ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 →
      ∀ theta : Fin N → ℝ,
        ‖(angularJacobian (constructedSelector b eta alpha) tau lam theta).det‖ ≤ C ^ N :=
  IsingBulk.Tail.constructed_selector_jacobian_bound b eta alpha tau
    hb heta hetaSmall halpha htau

/-- The real-smooth complete-factor estimate applies to coupled pair
functions of *all* coordinates.  It retains exact collision zeros and
never divides by an unchanged pair.  The analytic bounds and surviving
pair suppression remain explicit hypotheses of this product-rule lemma. -/
theorem coupled_complete_pair_jets
    {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq I]
    (edges : Finset I) (pair : I → E → ℂ) (x : E) (J : ℕ)
    (C B : ℝ) (hC : 1 ≤ C) (hB : 0 ≤ B)
    (hSmooth : ∀ e ∈ edges, ContDiffAt ℝ ∞ (pair e) x)
    (hJet : ∀ e ∈ edges, ∀ k, 0 < k → k ≤ J →
      ‖iteratedFDeriv ℝ k (pair e) x‖ ≤ C)
    (hRemaining : ∀ changed ⊆ edges, changed.card ≤ J →
      ∏ e ∈ edges \ changed, ‖pair e x‖ ≤ B)
    (k : ℕ) (hk : k ≤ J) :
    ‖iteratedFDeriv ℝ k (fun y => ∏ e ∈ edges, pair e y) x‖ ≤
      (edges.card : ℝ) ^ k * C ^ k * B :=
  IsingBulk.Tail.smooth_product_changed_factors_bound edges pair x J C B
    hC hB hSmooth hJet hRemaining k hk

end
end IsingBulk.HT.Tail
