import IsingBulk.Algebra.SchurPfaffian
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Tactic

namespace IsingBulk.Anisotropic.Algebra
noncomputable section

def schurKernel (x y : ℂ) : ℂ := (x-y)/(1-x*y)

theorem schurKernel_self (x : ℂ) : schurKernel x x = 0 := by
  simp [schurKernel]

theorem schurKernel_swap (x y : ℂ) : schurKernel y x = -schurKernel x y := by
  unfold schurKernel
  rw [mul_comm y x, ← neg_sub x y, neg_div]

theorem schurKernel_ne_zero {a b : ℂ} (hab : a ≠ b) (hd : 1-a*b ≠ 0) :
    schurKernel a b ≠ 0 := div_ne_zero (sub_ne_zero.mpr hab) hd

/-- Exact two-row elimination identity, including x=y. -/
theorem schurKernel_elimination (a b x y : ℂ)
    (hab : a ≠ b) (dab : 1-a*b ≠ 0)
    (dax : 1-a*x ≠ 0) (day : 1-a*y ≠ 0)
    (dbx : 1-b*x ≠ 0) (dby : 1-b*y ≠ 0) (dxy : 1-x*y ≠ 0) :
    schurKernel x y + schurKernel b x * schurKernel a y / schurKernel a b -
      schurKernel a x * schurKernel b y / schurKernel a b =
      (schurKernel a x * schurKernel b x) * schurKernel x y *
      (schurKernel a y * schurKernel b y) := by
  have hp := IsingBulk.Schur.fraction_four a b x y dab dax day dbx dby dxy
  simp [IsingBulk.Schur.pfaffian, IsingBulk.Schur.pairProduct] at hp
  change schurKernel a b * schurKernel x y + (- (schurKernel a x * schurKernel b y) +
    schurKernel a y * schurKernel b x) = schurKernel a b *
      (schurKernel a x * schurKernel a y) *
      (schurKernel b x * schurKernel b y * schurKernel x y) at hp
  have hk := schurKernel_ne_zero hab dab
  apply (mul_left_cancel₀ hk)
  simp only [mul_add, mul_sub, ← mul_div_assoc, mul_div_cancel_left₀ _ hk]
  linear_combination hp

end
end IsingBulk.Anisotropic.Algebra
