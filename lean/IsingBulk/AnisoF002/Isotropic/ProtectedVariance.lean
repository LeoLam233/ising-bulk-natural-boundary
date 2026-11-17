import IsingBulk.AnisoF002.Isotropic.VarianceCoercivity

/-!
# F002: quantitative protection of the complex variance

The complex bilinear variance need not be coercive on arbitrary tuples.
This file controls its change by actual pairwise perturbations, then
preserves the actual-contour real-part gap.  The finite-cardinality loss
is explicit, yielding the `diameter / N²` protected scale once the
analytic inverse's coordinate perturbation is supplied.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped BigOperators

/-- A square changes by at most the linear-plus-quadratic perturbation budget. -/
theorem square_perturbation_bound (z e : ℂ) (R δ : ℝ)
    (hδ : 0 ≤ δ) (hz : ‖z‖ ≤ R) (he : ‖e‖ ≤ δ) :
    ‖(z + e) ^ 2 - z ^ 2‖ ≤ δ * (2 * R + δ) := by
  have hid : (z + e) ^ 2 - z ^ 2 = e * (2 * z + e) := by ring
  rw [hid, norm_mul]
  have hb : ‖2 * z + e‖ ≤ 2 * R + δ := by
    calc
      ‖2 * z + e‖ ≤ ‖(2 : ℂ) * z‖ + ‖e‖ := norm_add_le _ _
      _ = 2 * ‖z‖ + ‖e‖ := by simp only [norm_mul]; norm_num
      _ ≤ 2 * R + δ := by linarith
  exact mul_le_mul he hb (norm_nonneg _) hδ

variable {ι : Type*} [Fintype ι]

/-- Complete variance perturbation; every pair is counted, without a chart truncation. -/
theorem pairVariance_perturbation_bound (U U' : ι → ℂ) (R δ : ℝ)
    (hδ : 0 ≤ δ)
    (hbase : ∀ i j, ‖U i - U j‖ ≤ R)
    (hpair : ∀ i j, ‖(U' i - U' j) - (U i - U j)‖ ≤ δ) :
    ‖pairVariance U' - pairVariance U‖ ≤
      ((Fintype.card ι : ℝ) ^ 2 / 2) * (δ * (2 * R + δ)) := by
  have hterm : ∀ i j, ‖(U' i - U' j) ^ 2 - (U i - U j) ^ 2‖ ≤
      δ * (2 * R + δ) := by
    intro i j
    have hb := square_perturbation_bound (U i - U j)
      ((U' i - U' j) - (U i - U j)) R δ hδ (hbase i j) (hpair i j)
    have hid : (U i - U j) + ((U' i - U' j) - (U i - U j)) = U' i - U' j := by ring
    rw [hid] at hb
    exact hb
  have hsum : ‖∑ i, ∑ j, ((U' i - U' j) ^ 2 - (U i - U j) ^ 2)‖ ≤
      (Fintype.card ι : ℝ) ^ 2 * (δ * (2 * R + δ)) := by
    calc
      ‖∑ i, ∑ j, ((U' i - U' j) ^ 2 - (U i - U j) ^ 2)‖ ≤
          ∑ i, ‖∑ j, ((U' i - U' j) ^ 2 - (U i - U j) ^ 2)‖ := norm_sum_le _ _
      _ ≤ ∑ i, ∑ j, ‖(U' i - U' j) ^ 2 - (U i - U j) ^ 2‖ := by
        exact Finset.sum_le_sum fun i _ => norm_sum_le _ _
      _ ≤ ∑ _i : ι, ∑ _j : ι, δ * (2 * R + δ) := by
        exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
      _ = (Fintype.card ι : ℝ) ^ 2 * (δ * (2 * R + δ)) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
  have hid : pairVariance U' - pairVariance U = (1 / 2 : ℂ) *
      ∑ i, ∑ j, ((U' i - U' j) ^ 2 - (U i - U j) ^ 2) := by
    simp only [pairVariance, Finset.sum_sub_distrib]
    ring
  rw [hid, norm_mul]
  have hh : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  rw [hh]
  calc
    (1 / 2 : ℝ) * ‖∑ i, ∑ j, ((U' i - U' j) ^ 2 - (U i - U j) ^ 2)‖ ≤
        (1 / 2 : ℝ) * ((Fintype.card ι : ℝ) ^ 2 * (δ * (2 * R + δ))) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ((Fintype.card ι : ℝ) ^ 2 / 2) * (δ * (2 * R + δ)) := by ring

/-- Coordinate perturbations give pair perturbations with the exact factor two. -/
theorem pairVariance_coordinate_perturbation (U U' : ι → ℂ) (R ε : ℝ)
    (hε : 0 ≤ ε)
    (hbase : ∀ i j, ‖U i - U j‖ ≤ R)
    (hcoord : ∀ i, ‖U' i - U i‖ ≤ ε) :
    ‖pairVariance U' - pairVariance U‖ ≤
      ((Fintype.card ι : ℝ) ^ 2 / 2) * (2 * ε * (2 * R + 2 * ε)) := by
  apply pairVariance_perturbation_bound U U' R (2 * ε) (by positivity) hbase
  intro i j
  have hid : (U' i - U' j) - (U i - U j) = (U' i - U i) - (U' j - U j) := by ring
  rw [hid]
  exact (norm_sub_le _ _).trans (by linarith [hcoord i, hcoord j])

/-- The protected neighborhood has nonzero denominator whenever its explicit
finite-dimensional budget uses at most half the actual real-part gap. -/
theorem pairVariance_protected_ne_zero (U U' : ι → ℂ) (R ε : ℝ)
    (hε : 0 ≤ ε)
    (hbase : ∀ i j, ‖U i - U j‖ ≤ R)
    (hcoord : ∀ i, ‖U' i - U i‖ ≤ ε)
    (hD : 0 < (pairVariance U).re)
    (hbudget : ((Fintype.card ι : ℝ) ^ 2 / 2) * (2 * ε * (2 * R + 2 * ε)) ≤
      (pairVariance U).re / 2) : pairVariance U' ≠ 0 := by
  exact protected_variance_ne_zero _ _ hD
    ((pairVariance_coordinate_perturbation U U' R ε hε hbase hcoord).trans hbudget)

end IsingBulk.AnisoF002.Isotropic
