import IsingBulk.AnisoF002.C03.RegularWindingSectorGeometry
import Mathlib.MeasureTheory.Group.Integral

/-!
# Exact centering of every winding sector on the independent-coordinate plane

Translation has Jacobian one in the first N-1 coordinates.  The target
measure is the genuine pushforward of that Lebesgue measure, not the
orthonormal hypersurface measure.  The Vandermonde is unchanged and the
quadratic cutoff becomes Q + pi^2 w^2/N exactly.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set MeasureTheory IsingBulk.AnisoF002.RegularTail.C03
open scoped BigOperators

def windingMean (n : ℕ) (w : ℤ) : ℝ := (w : ℝ) * Real.pi / (n + 1 : ℕ)

def centeredWindingAngles {n : ℕ} (w : ℤ) (v : Angular.constrainedPlane n) : Fin (n + 1) → ℝ :=
  fun i => windingMean n w + (v : Angular.Ambient n) i

theorem windingMean_mul (n : ℕ) (w : ℤ) :
    ((n + 1 : ℕ) : ℝ) * windingMean n w = (w : ℝ) * Real.pi := by
  unfold windingMean
  field_simp

theorem windingAngles_centered_shift (n : ℕ) (w : ℤ) (x : Fin n → ℝ) :
    windingAngles n w (x + fun _ => windingMean n w) =
      centeredWindingAngles w (Angular.independentChart n x) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [windingAngles_last, Pi.add_apply, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, centeredWindingAngles,
      Angular.independentChart_last]
    have hm := windingMean_mul n w
    push_cast at hm
    linear_combination -hm
  · simp only [windingAngles_castSucc, Pi.add_apply, centeredWindingAngles,
      Angular.independentChart_castSucc, add_comm]

theorem centeredWindingAngles_square {n : ℕ} (w : ℤ) (v : Angular.constrainedPlane n) :
    (∑ i, centeredWindingAngles w v i ^ 2) =
      ‖v‖ ^ 2 + (w : ℝ) ^ 2 * Real.pi ^ 2 / (n + 1 : ℕ) := by
  have hsum := Angular.constrained_sum v
  have hN : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  unfold centeredWindingAngles
  simp_rw [add_sq]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum,
    hsum, mul_zero, add_zero, ← Angular.constrained_norm_sq]
  unfold windingMean
  field_simp
  ring

theorem windingSquare_centered_shift (n : ℕ) (w : ℤ) (x : Fin n → ℝ) :
    windingSquare n w (x + fun _ => windingMean n w) =
      ‖Angular.independentChart n x‖ ^ 2 + (w : ℝ) ^ 2 * Real.pi ^ 2 / (n + 1 : ℕ) := by
  unfold windingSquare
  rw [windingAngles_centered_shift]
  exact centeredWindingAngles_square w _

theorem centeredWindingAngles_vandermonde {n : ℕ} (w : ℤ) (v : Angular.constrainedPlane n) :
    realWindingVandermondeSquared (n + 1) (centeredWindingAngles w v) =
      Angular.planeVandermonde v := by
  simp only [realWindingVandermondeSquared, centeredWindingAngles,
    Angular.planeVandermonde, IsingBulk.AnisoF002.RegularTail.vandermondeSquared,
    add_sub_add_left_eq_sub]

theorem windingSector_integral_center (n : ℕ) (w : ℤ) (s : ℝ)
    (F : (Fin (n + 1) → ℝ) → ℂ) :
    (∫ x : Fin n → ℝ, if windingSquare n w x ≤ s then F (windingAngles n w x) else 0) =
      ∫ v : Angular.constrainedPlane n,
        if ‖v‖ ^ 2 + (w : ℝ) ^ 2 * Real.pi ^ 2 / (n + 1 : ℕ) ≤ s then
          F (centeredWindingAngles w v) else 0 ∂Angular.independentMeasure n := by
  have htrans := integral_add_right_eq_self (μ := (volume : Measure (Fin n → ℝ)))
    (fun x : Fin n → ℝ => if windingSquare n w x ≤ s then F (windingAngles n w x) else 0)
    (fun _ => windingMean n w)
  rw [← htrans]
  simp_rw [windingSquare_centered_shift, windingAngles_centered_shift]
  exact (Angular.independentChart_measurePreserving n).integral_comp
    (Angular.independentChart n).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (fun v : Angular.constrainedPlane n =>
      if ‖v‖ ^ 2 + (w : ℝ) ^ 2 * Real.pi ^ 2 / (n + 1 : ℕ) ≤ s then
        F (centeredWindingAngles w v) else 0)

end
end IsingBulk.AnisoF002.NegativeHT
