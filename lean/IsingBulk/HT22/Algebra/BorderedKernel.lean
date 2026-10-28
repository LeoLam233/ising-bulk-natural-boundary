import IsingBulk.HT22.Algebra.DispersionGhost
import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.Logic.Equiv.Fin.Rotate

/-! # F001 constant-border algebra

A ghost-first representation is used for the induction. The actual last
constant border is obtained by simultaneous row/column cyclic permutation.
-/

namespace IsingBulk.HT22.Algebra
noncomputable section
open IsingBulk.Preferred22
open scoped BigOperators

/-- A skew border, with the ghost at index zero. -/
def ghostBorder {N : ℕ} (K : Matrix (Fin N) (Fin N) ℂ) (r : Fin N → ℂ) :
    Matrix (Fin (N+1)) (Fin (N+1)) ℂ :=
  Fin.cons (Fin.cons 0 r) (fun i => Fin.cons (-r i) (K i))

@[simp] theorem ghostBorder_zero_zero {N : ℕ}
    (K : Matrix (Fin N) (Fin N) ℂ) (r : Fin N → ℂ) :
    ghostBorder K r 0 0 = 0 := rfl
@[simp] theorem ghostBorder_zero_succ {N : ℕ}
    (K : Matrix (Fin N) (Fin N) ℂ) (r : Fin N → ℂ) (j : Fin N) :
    ghostBorder K r 0 j.succ = r j := by simp [ghostBorder]
@[simp] theorem ghostBorder_succ_zero {N : ℕ}
    (K : Matrix (Fin N) (Fin N) ℂ) (r : Fin N → ℂ) (i : Fin N) :
    ghostBorder K r i.succ 0 = -r i := by simp [ghostBorder]
@[simp] theorem ghostBorder_succ_succ {N : ℕ}
    (K : Matrix (Fin N) (Fin N) ℂ) (r : Fin N → ℂ) (i j : Fin N) :
    ghostBorder K r i.succ j.succ = K i j := by simp [ghostBorder]

/-- Ordinary entries without square roots, exactly `L` from F001. -/
def ordinaryEntry (yi yj zi zj : ℂ) : ℂ :=
  -Complex.I * dispersionB yi yj zi zj

/-- The rational physical pair square. -/
def physicalPair (yi yj zi zj : ℂ) : ℂ :=
  -(zi/yi)*(zj/yj)*(dispersionB yi yj zi zj)^2

/-- The manuscript's formula, with all denominators literal and totalized. -/
theorem physicalPair_eq (yi yj zi zj : ℂ) :
    physicalPair yi yj zi zj =
      -((yi-yj)^2*zi*zj)/(yi*yj*(1-zi*zj)^2) := by
  unfold physicalPair dispersionB
  simp only [div_eq_mul_inv, mul_inv_rev, ← inv_pow]
  ring

/-- This finite algebraic scaling uses roots only internally. -/
theorem scaledPair_sq (yi yj zi zj ri rj : ℂ)
    (hi : ri^2 = zi/yi) (hj : rj^2 = zj/yj) :
    (scaledPair ri rj (dispersionB yi yj zi zj))^2 =
      physicalPair yi yj zi zj := by
  unfold scaledPair physicalPair
  rw [mul_pow, mul_pow, mul_pow, neg_sq, Complex.I_sq, hi, hj]
  ring

/-- The ghost border inherits alternation with no invertibility hypothesis. -/
theorem ghostBorder_skew {N : ℕ} (K : Matrix (Fin N) (Fin N) ℂ)
    (r : Fin N → ℂ) (hK : ∀ i j, K i j = -K j i) :
    ∀ i j, ghostBorder K r i j = -ghostBorder K r j i := by
  intro i j
  cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp only [ghostBorder_zero_zero, ghostBorder_zero_succ,
      ghostBorder_succ_zero, ghostBorder_succ_succ, neg_neg, neg_zero]
  exact hK _ _

theorem ghostBorder_diagonal {N : ℕ} (K : Matrix (Fin N) (Fin N) ℂ)
    (r : Fin N → ℂ) (hK : ∀ i, K i i = 0) :
    ∀ i, ghostBorder K r i i = 0 := by
  intro i
  cases i using Fin.cases <;> simp [hK]

/-- All four-point equations of the enlarged matrix follow from the ordinary
four-point equations and the new three-point ghost equation. -/
theorem ghostBorder_four_point {N : ℕ} (K : Matrix (Fin N) (Fin N) ℂ)
    (r : Fin N → ℂ)
    (hfour : ∀ a b i j,
      K a b*K i j-K a i*K b j+K a j*K b i =
      K a b*K a i*K a j*K b i*K b j*K i j)
    (hthree : ∀ a b c,
      r a*K b c-r b*K a c+r c*K a b =
      r a*r b*r c*K a b*K a c*K b c) :
    ∀ a b i j,
      ghostBorder K r a b*ghostBorder K r i j-
        ghostBorder K r a i*ghostBorder K r b j+
        ghostBorder K r a j*ghostBorder K r b i =
      ghostBorder K r a b*ghostBorder K r a i*ghostBorder K r a j*
        ghostBorder K r b i*ghostBorder K r b j*ghostBorder K r i j := by
  intro a b i j
  cases a using Fin.cases <;> cases b using Fin.cases <;>
    cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp only [ghostBorder_zero_zero, ghostBorder_zero_succ,
      ghostBorder_succ_zero, ghostBorder_succ_succ]
  all_goals try (solve | ring)
  · rename_i a b c; linear_combination hthree a b c
  · rename_i a b c; linear_combination -(hthree a b c)
  · rename_i a b c; linear_combination hthree a b c
  · rename_i a b c; linear_combination -(hthree a b c)
  · rename_i a b c d; linear_combination hfour a b c d

end
end IsingBulk.HT22.Algebra
