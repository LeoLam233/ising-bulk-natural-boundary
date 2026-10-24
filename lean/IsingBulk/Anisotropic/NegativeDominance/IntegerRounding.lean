import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-! The integer-rounding part of the balanced-order selection. The analytic
sign and derivative estimates must be proved for the exact model separately. -/
namespace IsingBulk.Anisotropic.NegativeDominance
open Set

/-- Rounding a nonnegative real zero down loses at most the derivative bound.
The derivative is required on the one-unit enlarged interval, so rounding
never implicitly leaves the region where the estimate holds. -/
theorem floor_balance_bound (F F' : ℝ → ℝ) {L H x C : ℝ}
    (hx0 : 0 ≤ x) (hx : x ∈ Icc L H) (hzero : F x = 0) (hC : 0 ≤ C)
    (hd : ∀ y ∈ Icc (L - 1) H, HasDerivWithinAt F (F' y) (Icc (L - 1) H) y)
    (hb : ∀ y ∈ Icc (L - 1) H, ‖F' y‖ ≤ C) :
    L - 1 < (Nat.floor x : ℝ) ∧ (Nat.floor x : ℝ) ≤ H ∧
      |F (Nat.floor x)| ≤ C := by
  have hlo := Nat.lt_floor_add_one x
  have hhi := Nat.floor_le hx0
  have hfloor : (Nat.floor x : ℝ) ∈ Icc (L - 1) H := ⟨by linarith [hx.1], hhi.trans hx.2⟩
  have hreal : x ∈ Icc (L - 1) H := ⟨by linarith [hx.1], hx.2⟩
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb
    (convex_Icc (L - 1) H) hreal hfloor
  rw [hzero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr hhi)] at hm
  refine ⟨by linarith [hx.1], hfloor.2, hm.trans ?_⟩
  calc
    C * -((Nat.floor x : ℝ) - x) ≤ C * 1 := mul_le_mul_of_nonneg_left (by linarith) hC
    _ = C := mul_one C

/-- A sign-changing real balance function supplies a genuine natural order
with controlled imbalance. This is an IVT/rounding lemma, not an assertion
that the ANISO model satisfies its analytic premises. -/
theorem exists_nat_balanced_of_sign_change (F F' : ℝ → ℝ) {L H C : ℝ}
    (hL : 0 ≤ L) (hLH : L ≤ H) (hc : ContinuousOn F (Icc L H))
    (hl : F L ≤ 0) (hh : 0 ≤ F H) (hC : 0 ≤ C)
    (hd : ∀ y ∈ Icc (L - 1) H, HasDerivWithinAt F (F' y) (Icc (L - 1) H) y)
    (hb : ∀ y ∈ Icc (L - 1) H, ‖F' y‖ ≤ C) :
    ∃ j : ℕ, L - 1 < (j : ℝ) ∧ (j : ℝ) ≤ H ∧ |F j| ≤ C := by
  obtain ⟨x, hx, hzero⟩ := intermediate_value_Icc hLH hc ⟨hl, hh⟩
  exact ⟨Nat.floor x, floor_balance_bound F F' (hL.trans hx.1) hx hzero hC hd hb⟩

end IsingBulk.Anisotropic.NegativeDominance
