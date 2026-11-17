import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The F002 endpoint defect

This is a new derivation of the polynomial identity used in F002 §2.3.
No historical ANISO geometry theorem is imported.  In the notation of the
paper, `h,c,H,C` are the two sinh/cosh pairs and `t,q,v,w` the two cosine/sine
pairs.  The identity retains `D = 0`: no division is performed.  On an edge
`F₁ = 0`, a nonzero second edge factor forces both the Cramer determinant
and the endpoint defect to be strictly positive.

This file does not prove the global spectral-set geometry or density theorem.
-/

namespace IsingBulk.AnisoF002.Geometry

def detExpr (h c H C t q v w : ℝ) : ℝ := h * C * t * w - c * H * q * v

def numExpr (h c H C t q v w : ℝ) : ℝ := c * t * v * w - h * H * C * q

def firstEdge (c H C t : ℝ) : ℝ := C ^ 2 * t ^ 2 - c ^ 2 * H ^ 2

def secondEdge (h c C v : ℝ) : ℝ := c ^ 2 * v ^ 2 - h ^ 2 * C ^ 2

theorem numerator_difference (h c H C t q v w : ℝ) :
    numExpr h c H C t q v w ^ 2 - detExpr h c H C t q v w ^ 2 =
      secondEdge h c C v * (t ^ 2 * w ^ 2 - H ^ 2 * q ^ 2) := by
  unfold numExpr detExpr secondEdge
  ring

theorem auxiliary_factor (h c H C t q v w : ℝ)
    (hc : c ^ 2 - h ^ 2 = 1) (hC : C ^ 2 - H ^ 2 = 1)
    (ht : t ^ 2 + q ^ 2 = 1) (hv : v ^ 2 + w ^ 2 = 1) :
    C ^ 2 * (t ^ 2 * w ^ 2 - H ^ 2 * q ^ 2) =
      (C ^ 2 - v ^ 2) * firstEdge c H C t - H ^ 2 * secondEdge h c C v := by
  unfold firstEdge secondEdge
  linear_combination C ^ 2 * t ^ 2 * hv - C ^ 2 * t ^ 2 * hC +
    C ^ 2 * H ^ 2 * hc - C ^ 2 * H ^ 2 * ht

theorem endpoint_defect_identity (h c H C t q v w : ℝ)
    (hc : c ^ 2 - h ^ 2 = 1) (hC : C ^ 2 - H ^ 2 = 1)
    (ht : t ^ 2 + q ^ 2 = 1) (hv : v ^ 2 + w ^ 2 = 1) :
    C ^ 2 * (detExpr h c H C t q v w ^ 2 - numExpr h c H C t q v w ^ 2) =
      H ^ 2 * secondEdge h c C v ^ 2 -
        (C ^ 2 - v ^ 2) * firstEdge c H C t * secondEdge h c C v := by
  linear_combination -C ^ 2 * numerator_difference h c H C t q v w -
    secondEdge h c C v * auxiliary_factor h c H C t q v w hc hC ht hv

theorem edge_defect_identity (h c H C t q v w u : ℝ)
    (hc : c ^ 2 - h ^ 2 = 1) (hC : C ^ 2 - H ^ 2 = 1)
    (ht : t ^ 2 + q ^ 2 = 1) (hv : v ^ 2 + w ^ 2 = 1)
    (hedge : firstEdge c H C t = 0)
    (hcoord : numExpr h c H C t q v w = detExpr h c H C t q v w * u) :
    C ^ 2 * detExpr h c H C t q v w ^ 2 * (1 - u ^ 2) =
      H ^ 2 * secondEdge h c C v ^ 2 := by
  have hdef := endpoint_defect_identity h c H C t q v w hc hC ht hv
  rw [hedge, mul_zero, zero_mul, sub_zero, hcoord] at hdef
  convert hdef using 1
  ring

theorem regular_edge_strict_coordinate (h c H C t q v w u : ℝ)
    (hc : c ^ 2 - h ^ 2 = 1) (hC : C ^ 2 - H ^ 2 = 1)
    (ht : t ^ 2 + q ^ 2 = 1) (hv : v ^ 2 + w ^ 2 = 1)
    (hedge : firstEdge c H C t = 0)
    (hcoord : numExpr h c H C t q v w = detExpr h c H C t q v w * u)
    (hH : H ≠ 0) (hsecond : secondEdge h c C v ≠ 0) :
    detExpr h c H C t q v w ≠ 0 ∧ |u| < 1 := by
  have hdef := edge_defect_identity h c H C t q v w u hc hC ht hv hedge hcoord
  have hrhs : 0 < H ^ 2 * secondEdge h c C v ^ 2 :=
    mul_pos (sq_pos_of_ne_zero hH) (sq_pos_of_ne_zero hsecond)
  have hprod : 0 < C ^ 2 * detExpr h c H C t q v w ^ 2 * (1 - u ^ 2) :=
    hdef.symm ▸ hrhs
  have hd : detExpr h c H C t q v w ≠ 0 := by
    intro hz
    rw [hz] at hprod
    norm_num at hprod
  have hpositive : 0 < 1 - u ^ 2 := by
    by_contra hn
    have hn' : 1 - u ^ 2 ≤ 0 := le_of_not_gt hn
    have hh := mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (sq_nonneg C) (sq_nonneg (detExpr h c H C t q v w))) hn'
    linarith
  refine ⟨hd, abs_lt.mpr ⟨?_, ?_⟩⟩ <;> nlinarith [sq_nonneg (u + 1), sq_nonneg (u - 1)]

/-- Direct substitution of the hyperbolic/trigonometric data.  This is the
F002 defect at every finite real `x,y,lam`; no exclusion of `lam = 1` or
nonzero determinant is hidden in the algebraic identity. -/
theorem hyperbolic_endpoint_defect (lam x y : ℝ) :
    let h := Real.sinh x
    let c := Real.cosh x
    let H := Real.sinh (lam * x)
    let C := Real.cosh (lam * x)
    let t := Real.cos y
    let q := Real.sin y
    let v := Real.cos (lam * y)
    let w := Real.sin (lam * y)
    C ^ 2 * (detExpr h c H C t q v w ^ 2 - numExpr h c H C t q v w ^ 2) =
      H ^ 2 * secondEdge h c C v ^ 2 -
        (C ^ 2 - v ^ 2) * firstEdge c H C t * secondEdge h c C v := by
  exact endpoint_defect_identity _ _ _ _ _ _ _ _
    (Real.cosh_sq_sub_sinh_sq x) (Real.cosh_sq_sub_sinh_sq (lam * x))
    (Real.cos_sq_add_sin_sq y) (Real.cos_sq_add_sin_sq (lam * y))

end IsingBulk.AnisoF002.Geometry
