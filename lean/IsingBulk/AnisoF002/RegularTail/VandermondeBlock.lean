import IsingBulk.AnisoF002.Isotropic.CellContraction
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The retained squared Vandermonde block

The product contains every unordered pair of the fixed block exactly once.
Its exact scaling degree and radial bound are checked here.  The factorization
of the complete differentiated physical numerator by this product remains a
separate analytic obligation; it is not an assumption of a final theorem.
-/

namespace IsingBulk.AnisoF002.RegularTail
open scoped BigOperators
open IsingBulk.AnisoF002.Isotropic

def vandermondeSquared {m : ℕ} (q : Fin m → ℝ) : ℝ :=
  ∏ ij ∈ indexPairs m, (q ij.1 - q ij.2) ^ 2

noncomputable def retainedSineBlock {m : ℕ} (q : Fin m → ℝ) : ℝ :=
  ∏ ij ∈ indexPairs m, Real.sin ((q ij.1 - q ij.2) / 2) ^ 2

theorem vandermondeSquared_nonneg {m : ℕ} (q : Fin m → ℝ) :
    0 ≤ vandermondeSquared q := by
  exact Finset.prod_nonneg (fun ij _ => sq_nonneg (q ij.1 - q ij.2))

theorem vandermonde_degree (m : ℕ) :
    (2 : ℝ) * (m.choose 2 : ℝ) = (m : ℝ) ^ 2 - m := by
  rw [Nat.cast_choose_two]
  ring

theorem vandermonde_scaling {m : ℕ} (q : Fin m → ℝ) (r : ℝ) :
    vandermondeSquared (fun i => r * q i) =
      r ^ (2 * m.choose 2) * vandermondeSquared q := by
  unfold vandermondeSquared
  simp_rw [← mul_sub, mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_const, card_indexPairs, ← pow_mul]

theorem coordinate_square_le_sum {m : ℕ} (q : Fin m → ℝ) (i : Fin m) :
    q i ^ 2 ≤ ∑ k, q k ^ 2 :=
  Finset.single_le_sum (fun k _ => sq_nonneg (q k)) (Finset.mem_univ i)

theorem vandermonde_radial_bound {m : ℕ} (q : Fin m → ℝ) (R : ℝ)
    (hR : (∑ k, q k ^ 2) ≤ R ^ 2) :
    vandermondeSquared q ≤ (4 * R ^ 2) ^ (m.choose 2) := by
  calc
    vandermondeSquared q ≤ ∏ _ij ∈ indexPairs m, (4 * R ^ 2) := by
      apply Finset.prod_le_prod₀ (fun ij _ => sq_nonneg (q ij.1 - q ij.2))
      intro ij _
      have hi := (coordinate_square_le_sum q ij.1).trans hR
      have hj := (coordinate_square_le_sum q ij.2).trans hR
      nlinarith [sq_nonneg (q ij.1 + q ij.2)]
    _ = (4 * R ^ 2) ^ (m.choose 2) := by
      rw [Finset.prod_const, card_indexPairs]

/-- The literal sine block in F002, with the normalization by 2 retained. -/
theorem retained_sine_le_vandermonde {m : ℕ} (q : Fin m → ℝ) :
    retainedSineBlock q ≤ (1 / 4 : ℝ) ^ (m.choose 2) * vandermondeSquared q := by
  calc
    retainedSineBlock q ≤ ∏ ij ∈ indexPairs m, ((q ij.1 - q ij.2) / 2) ^ 2 := by
      apply Finset.prod_le_prod₀ (fun ij _ => sq_nonneg (Real.sin ((q ij.1 - q ij.2) / 2)))
      intro ij _
      exact Real.sin_sq_le_sq
    _ = (1 / 4 : ℝ) ^ (m.choose 2) * vandermondeSquared q := by
      simp_rw [show ∀ x : ℝ, (x / 2) ^ 2 = (1 / 4 : ℝ) * x ^ 2 by intro x; ring]
      rw [Finset.prod_mul_distrib, Finset.prod_const, card_indexPairs]
      rfl

theorem retained_sine_radial_bound {m : ℕ} (q : Fin m → ℝ) (R : ℝ)
    (hR : (∑ k, q k ^ 2) ≤ R ^ 2) :
    retainedSineBlock q ≤ R ^ (2 * m.choose 2) := by
  calc
    retainedSineBlock q ≤ ∏ _ij ∈ indexPairs m, R ^ 2 := by
      apply Finset.prod_le_prod₀ (fun ij _ => sq_nonneg (Real.sin ((q ij.1 - q ij.2) / 2)))
      intro ij _
      have hi := (coordinate_square_le_sum q ij.1).trans hR
      have hj := (coordinate_square_le_sum q ij.2).trans hR
      have hs : Real.sin ((q ij.1 - q ij.2) / 2) ^ 2 ≤
          ((q ij.1 - q ij.2) / 2) ^ 2 := Real.sin_sq_le_sq
      nlinarith [sq_nonneg (q ij.1 + q ij.2)]
    _ = R ^ (2 * m.choose 2) := by
      rw [Finset.prod_const, card_indexPairs, ← pow_mul]

end IsingBulk.AnisoF002.RegularTail
