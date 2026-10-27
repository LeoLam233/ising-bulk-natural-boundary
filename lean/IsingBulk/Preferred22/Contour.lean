import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Basic.Complex.BigOperators
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! LT22 Section 5: the actual balanced displacement, its differential,
and the complete three-weight partition. These are pointwise identities;
the holomorphic homotopy and integral estimates are separate obligations. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators
open Complex

def occupancy {N : ℕ} (p : ℝ → ℝ) (θ : Fin N → ℝ) : ℝ := ∑ i, p (θ i)

def balancedShift {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ) (θ : Fin N → ℝ) (i : Fin N) : ℝ :=
  τ / N * (occupancy p θ * m (θ i) - occupancy m θ * p (θ i))

theorem balancedShift_sum {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ) (θ : Fin N → ℝ) :
    ∑ i, balancedShift τ p m θ i = 0 := by
  simp only [balancedShift, Finset.sum_sub_distrib, ← Finset.mul_sum]
  unfold occupancy
  ring

def deformedAngles {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ) (θ : Fin N → ℝ) (i : Fin N) : ℂ :=
  (θ i : ℂ) - Complex.I * balancedShift τ p m θ i

theorem deformedAngles_sum {N : ℕ} (τ : ℝ) (p m : ℝ → ℝ) (θ : Fin N → ℝ) :
    ∑ i, deformedAngles τ p m θ i = ∑ i, (θ i : ℂ) := by
  simp only [deformedAngles, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Complex.ofReal_sum, balancedShift_sum, Complex.ofReal_zero, mul_zero, sub_zero]

theorem balancedShift_at_equality {N : ℕ} (τ t : ℝ) (p m : ℝ → ℝ) (i : Fin N) :
    balancedShift τ p m (fun _ => t) i = 0 := by
  simp only [balancedShift, occupancy, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

theorem balancedShift_reflection {N : ℕ} (τ : ℝ) (p : ℝ → ℝ) (θ : Fin N → ℝ)
    (i : Fin N) :
    balancedShift τ p (fun x => p (-x)) (fun j => -θ j) i =
      -balancedShift τ p (fun x => p (-x)) θ i := by
  simp [balancedShift, occupancy]
  ring

/-- Entrywise differential of (5.1). `dp` and `dm` denote the actual bump derivatives. -/
def shiftJacobian {N : ℕ} (τ : ℝ) (p m dp dm : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => τ / N *
    ((if i = j then (∑ v, p v) * dm i - (∑ v, m v) * dp i else 0) +
      m i * dp j - p i * dm j)

theorem shiftJacobian_column_sum {N : ℕ} (τ : ℝ) (p m dp dm : Fin N → ℝ)
    (j : Fin N) : ∑ i, shiftJacobian τ p m dp dm i j = 0 := by
  simp only [shiftJacobian, ← Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    ← Finset.sum_mul]
  ring

theorem shiftJacobian_maps_to_zero_sum {N : ℕ} (τ : ℝ) (p m dp dm v : Fin N → ℝ) :
    ∑ i, (shiftJacobian τ p m dp dm).mulVec v i = 0 := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, shiftJacobian_column_sum, zero_mul, Finset.sum_const_zero]

def fullWeight (a b : ℝ) : ℝ := a * b
def lowerWeight (a b : ℝ) : ℝ := (1 - a) * (1 + b) / 2
def upperWeight (a b : ℝ) : ℝ := (1 - b) * (1 + a) / 2

theorem full_partition (a b : ℝ) : fullWeight a b + lowerWeight a b + upperWeight a b = 1 := by
  unfold fullWeight lowerWeight upperWeight
  ring

theorem reflected_weights (a b : ℝ) : lowerWeight b a = upperWeight a b := rfl

theorem partition_nonnegative {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    0 ≤ fullWeight a b ∧ 0 ≤ lowerWeight a b ∧ 0 ≤ upperWeight a b := by
  unfold fullWeight lowerWeight upperWeight
  exact ⟨mul_nonneg ha0 hb0,
    div_nonneg (mul_nonneg (sub_nonneg.mpr ha1) (by linarith)) (by norm_num),
    div_nonneg (mul_nonneg (sub_nonneg.mpr hb1) (by linarith)) (by norm_num)⟩

/-- A literal parameterization of the entire homotopy, before localization. -/
def homotopyRoot {N : ℕ} (τ lam : ℝ) (p m : ℝ → ℝ) (θ : Fin N → ℝ) (i : Fin N) : ℂ :=
  Complex.exp (Complex.I * θ i + lam * balancedShift τ p m θ i)

theorem homotopy_product_preserved {N : ℕ} (τ lam : ℝ) (p m : ℝ → ℝ) (θ : Fin N → ℝ) :
    ∏ i, homotopyRoot τ lam p m θ i = ∏ i, Complex.exp (Complex.I * θ i) := by
  unfold homotopyRoot
  rw [← Complex.exp_sum, ← Complex.exp_sum]
  congr 1
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Complex.ofReal_sum,
    balancedShift_sum, Complex.ofReal_zero, mul_zero, add_zero]

end
end IsingBulk.Preferred22
