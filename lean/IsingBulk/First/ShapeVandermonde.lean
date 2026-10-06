import IsingBulk.First.ShapeGeometry
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Cast

/-! The actual squared Vandermonde on the Euclidean shape hyperplane. -/
namespace IsingBulk.First
noncomputable section
open MeasureTheory Module
open scoped BigOperators InnerProductSpace

/-- Each ordered source pair appears exactly once. -/
def firstStrictPairs (N : ℕ) : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun p => p.1 < p.2)

@[simp] theorem mem_firstStrictPairs {N : ℕ} (p : Fin N × Fin N) :
    p ∈ firstStrictPairs N ↔ p.1 < p.2 := by simp [firstStrictPairs]

theorem firstStrictPairs_card (N : ℕ) : (firstStrictPairs N).card = N.choose 2 := by
  simpa [firstStrictPairs] using (Fintype.card_product_filter_lt (α := Fin N))

theorem firstStrictPairs_twice_card (n : ℕ) :
    2 * (firstStrictPairs (n+1)).card = (n+1) * n := by
  rw [firstStrictPairs_card]
  have h := Nat.descFactorial_eq_factorial_mul_choose (n+1) 2
  norm_num [Nat.descFactorial_succ] at h
  simpa [mul_comm] using h.symm

/-- Source ordering of the differences, with no determinant sign convention. -/
def firstVandermonde {N : ℕ} (x : Fin N → ℝ) : ℝ :=
  ∏ p ∈ firstStrictPairs N, (x p.1 - x p.2)

theorem firstVandermonde_nonzero {N : ℕ} {x : Fin N → ℝ} (hx : Function.Injective x) :
    firstVandermonde x ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact sub_ne_zero.mpr (fun h => (ne_of_lt (mem_firstStrictPairs p |>.mp hp)) (hx h))

theorem firstVandermonde_scale {N : ℕ} (r : ℝ) (x : Fin N → ℝ) :
    firstVandermonde (fun i => r * x i) =
      r ^ (N.choose 2) * firstVandermonde x := by
  simp [firstVandermonde, ← mul_sub, Finset.prod_mul_distrib, firstStrictPairs_card]

theorem firstVandermonde_continuous (N : ℕ) : Continuous (@firstVandermonde N) := by
  unfold firstVandermonde
  fun_prop

/-- The source squared numerator on the intrinsic hyperplane. -/
def shapeVandermondeSq {n : ℕ} (x : ShapeSpace n) : ℝ :=
  (firstVandermonde (fun i => x.1 i)) ^ 2

theorem shapeVandermondeSq_nonneg {n : ℕ} (x : ShapeSpace n) :
    0 ≤ shapeVandermondeSq x := sq_nonneg _

theorem shapeVandermondeSq_continuous (n : ℕ) :
    Continuous (@shapeVandermondeSq n) := by
  unfold shapeVandermondeSq
  apply Continuous.pow
  exact (firstVandermonde_continuous _).comp (by fun_prop)

theorem shapeVandermondeSq_scale {n : ℕ} (r : ℝ) (x : ShapeSpace n) :
    shapeVandermondeSq (r • x) =
      r ^ (2 * ((n+1).choose 2)) * shapeVandermondeSq x := by
  unfold shapeVandermondeSq
  change (firstVandermonde (fun i => r * x.1 i)) ^ 2 = _
  rw [firstVandermonde_scale, mul_pow, ← pow_mul, Nat.mul_comm]

theorem shapeVandermondeSq_homogeneous {n : ℕ} (r : ℝ) (x : ShapeSpace n) :
    shapeVandermondeSq (r • x) = r ^ ((n+1) * n) * shapeVandermondeSq x := by
  rw [shapeVandermondeSq_scale]
  have h := firstStrictPairs_twice_card n
  rw [firstStrictPairs_card] at h
  rw [h]

/-- Centering distinct real labels supplies a genuinely zero-sum witness. -/
def distinctShape (n : ℕ) : ShapeSpace n :=
  ⟨WithLp.toLp 2 (shapeCoordinates (fun i : Fin (n+1) => (i : ℝ))),
    sum_shapeCoordinates (by positivity) _⟩

theorem distinctShape_injective (n : ℕ) : Function.Injective (fun i => (distinctShape n).1 i) := by
  intro i j h
  change (i : ℝ) - _ = (j : ℝ) - _ at h
  have hij : (i : ℝ) = (j : ℝ) := sub_left_injective h
  exact Fin.ext (by exact_mod_cast hij)

theorem distinctShape_ne_zero {n : ℕ} (hn : 1 ≤ n) : distinctShape n ≠ 0 := by
  intro h
  have he : (distinctShape n).1 0 = (distinctShape n).1 (Fin.last n) := by rw [h]; rfl
  have hi := distinctShape_injective n he
  have hv := congrArg Fin.val hi
  simp at hv
  omega

/-- A point on the actual Euclidean unit sphere where every coordinate is distinct. -/
def distinctShapeUnit {n : ℕ} (hn : 1 ≤ n) : Metric.sphere (0 : ShapeSpace n) 1 :=
  ⟨‖distinctShape n‖⁻¹ • distinctShape n, by
    rw [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _)), inv_mul_cancel₀]
    exact norm_ne_zero_iff.mpr (distinctShape_ne_zero hn)⟩

theorem shapeVandermondeSq_distinctShapeUnit_ne_zero {n : ℕ} (hn : 1 ≤ n) :
    shapeVandermondeSq (distinctShapeUnit hn).1 ≠ 0 := by
  apply pow_ne_zero
  apply firstVandermonde_nonzero
  intro i j h
  have he : (distinctShape n).1 i = (distinctShape n).1 j :=
    mul_left_cancel₀ (inv_ne_zero (norm_ne_zero_iff.mpr (distinctShape_ne_zero hn))) h
  exact distinctShape_injective n he

end
end IsingBulk.First
