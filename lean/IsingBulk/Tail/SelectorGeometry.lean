import IsingBulk.First.InteriorRoot
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic

/-! Pointwise geometry and exact Jacobian of the source weighted retraction.
No integral identity or uniform bound is an assumption here. -/
namespace IsingBulk.Tail
noncomputable section
open scoped BigOperators
open IsingBulk.First

def occupancy {N : ℕ} (p : Fin N → ℝ) : ℝ := ∑ i, p i

def retractionShift {N : ℕ} (τ : ℝ) (p m : Fin N → ℝ) (i : Fin N) : ℝ :=
  -2*τ*p i + τ*occupancy p/(2*N)*m i

def selectorWeight {N : ℕ} (a : Fin N → ℝ) : ℝ := ∏ i, (1-a i)

theorem occupancy_nonneg {N : ℕ} {p : Fin N → ℝ} (hp : ∀ i, 0 ≤ p i) :
    0 ≤ occupancy p := Finset.sum_nonneg (fun i _ => hp i)

theorem occupancy_le {N : ℕ} {p : Fin N → ℝ} (hp : ∀ i, p i ≤ 1) :
    occupancy p ≤ N := by
  simpa [occupancy] using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hp i)

theorem occupancy_named {N : ℕ} {p : Fin N → ℝ} (hp : ∀ i, 0 ≤ p i)
    (q : Fin N) (hq : p q = 1) : 1 ≤ occupancy p := by
  rw [← hq]
  exact Finset.single_le_sum (fun i _ => hp i) (Finset.mem_univ q)

theorem sum_retractionShift {N : ℕ} (τ : ℝ) (p m : Fin N → ℝ) :
    ∑ i, retractionShift τ p m i =
      -2*τ*occupancy p + τ*occupancy p/(2*N)*∑ i, m i := by
  simp [retractionShift, Finset.sum_add_distrib, ← Finset.mul_sum, occupancy]

theorem sum_retractionShift_le {N : ℕ} (hN : 0 < N) {τ : ℝ} (hτ : 0 ≤ τ)
    {p m : Fin N → ℝ} (hp : ∀ i, 0 ≤ p i) (hm : ∀ i, m i ≤ 1) :
    ∑ i, retractionShift τ p m i ≤ -3*τ*occupancy p/2 := by
  rw [sum_retractionShift]
  have hn : (0:ℝ) < N := by exact_mod_cast hN
  have hsum : (∑ i, m i) ≤ (N:ℝ) := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hm i)
  have hP := occupancy_nonneg hp
  have hc : 0 ≤ τ*occupancy p/(2*N) := by positivity
  have hh := mul_le_mul_of_nonneg_left hsum hc
  have he : τ*occupancy p/(2*N)*(N:ℝ) = τ*occupancy p/2 := by field_simp
  rw [he] at hh
  linarith

theorem retractionShift_named {N : ℕ} (τ : ℝ) (p m : Fin N → ℝ)
    (q : Fin N) (hp : p q = 1) (hm : m q = 0) :
    retractionShift τ p m q = -2*τ := by simp [retractionShift, hp, hm]

/-- The source normalized angular Jacobian, before integration. -/
def retractionJacobian {N : ℕ} (lam τ : ℝ) (p m p' m' : Fin N → ℝ) :
    Matrix (Fin N) (Fin N) ℂ := fun i j =>
  (if i=j then Complex.I + (lam*(-2*τ*p' i+τ*occupancy p/(2*N)*m' i) : ℝ) else 0) +
    (lam*τ/(2*N)*m i*p' j : ℝ)

theorem retractionJacobian_named_column {N : ℕ} (lam τ : ℝ)
    (p m p' m' : Fin N → ℝ) (q : Fin N) (hp' : p' q = 0) (hm' : m' q = 0) :
    ∀ i, retractionJacobian lam τ p m p' m' i q = if i=q then Complex.I else 0 := by
  intro i
  by_cases hi : i=q
  · subst i; simp [retractionJacobian, hp', hm']
  · simp [retractionJacobian, hi, hp']

theorem retractionJacobian_named_row {N : ℕ} (lam τ : ℝ)
    (p m p' m' : Fin N → ℝ) (q : Fin N)
    (hp' : p' q = 0) (hm : m q = 0) (hm' : m' q = 0) :
    ∀ i, retractionJacobian lam τ p m p' m' q i = if q=i then Complex.I else 0 := by
  intro i
  simp [retractionJacobian, hp', hm, hm']

/-- The sign and factor in the source current come from division by i. -/
theorem named_velocity_ratio (τ : ℝ) : (-2*(τ:ℂ))/Complex.I = 2*Complex.I*τ := by
  apply (div_eq_iff Complex.I_ne_zero).mpr
  calc
    -2*(τ:ℂ) = (2*(Complex.I*Complex.I))*(τ:ℂ) := by rw [Complex.I_mul_I]; ring
    _ = 2*Complex.I*τ*Complex.I := by ring

end
end IsingBulk.Tail
