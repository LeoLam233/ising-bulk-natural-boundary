import IsingBulk.Algebra.PrimeTheorem
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Exact limiting-torus geometry for FIRST, manuscript lines 607–623.
These are algebraic ingredients, not an assumed complement estimate. -/
namespace IsingBulk.First
noncomputable section
open scoped BigOperators

/-- The two real coordinates of a unit complex number satisfy the unit equation. -/
theorem unit_coordinate_equation {z : ℂ} (hz : ‖z‖ = 1) :
    z.re ^ 2 + z.im ^ 2 = 1 := by
  have h := Complex.normSq_eq_norm_sq z
  rw [hz] at h
  simpa [Complex.normSq_apply, pow_two] using h

/-- On the strict lower unit semicircle the real coordinate is strictly interior. -/
theorem lower_unit_real_bounds {z : ℂ} (hz : ‖z‖ = 1) (hi : z.im < 0) :
    -1 < z.re ∧ z.re < 1 := by
  have he := unit_coordinate_equation hz
  have hp : 0 < z.im ^ 2 := sq_pos_of_ne_zero (ne_of_lt hi)
  constructor <;> nlinarith [sq_nonneg (z.re - 1), sq_nonneg (z.re + 1)]

/-- Lower-half-plane sign removes the ambiguity in reconstructing the imaginary part. -/
theorem lower_unit_eq_of_re_eq {z w : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1)
    (hzi : z.im < 0) (hwi : w.im < 0) (hr : z.re = w.re) : z = w := by
  apply Complex.ext hr
  have hez := unit_coordinate_equation hz
  have hew := unit_coordinate_equation hw
  rw [hr] at hez
  nlinarith

/-- An active pair factor on the unit torus has opposite imaginary coordinates. -/
theorem reciprocal_unit_imaginary_sum {z w : ℂ} (hz : ‖z‖ = 1)
    (hp : z * w = 1) : z.im + w.im = 0 := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hw : w = z⁻¹ := by
    apply (mul_left_cancel₀ hz0)
    simpa [hz0] using hp
  rw [hw, Complex.inv_eq_conj hz]
  simp

/-- Strict positivity needed in the source ratio argument, proved without differentiation. -/
theorem ratio_cross_factor_positive {a b c d : ℝ}
    (ha : -1 < a ∧ a < 1) (hb : -1 < b ∧ b < 1)
    (hc : -1 < c ∧ c < 1) (hd : -1 < d ∧ d < 1) :
    0 < 2 - a * d - c * b := by
  have had : a * d < 1 := by
    have h := mul_le_mul_of_nonneg_left (le_of_lt (abs_lt.mpr hd)) (abs_nonneg a)
    have h' := (abs_lt.mpr ha)
    have h'' : |a * d| < 1 := by rw [abs_mul]; nlinarith [abs_nonneg a]
    exact lt_of_le_of_lt (le_abs_self _) h''
  have hcb : c * b < 1 := by
    have h := mul_le_mul_of_nonneg_left (le_of_lt (abs_lt.mpr hb)) (abs_nonneg c)
    have h' := (abs_lt.mpr hc)
    have h'' : |c * b| < 1 := by rw [abs_mul]; nlinarith [abs_nonneg c]
    exact lt_of_le_of_lt (le_abs_self _) h''
  linarith

/-- Equal imaginary ratios determine the actual lower-torus dispersion pair.
This is source-equivalent to strict monotonicity along the positive level curve. -/
theorem lower_dispersion_ratio_injective {x y x' y' : ℂ} {S : ℝ}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hx' : ‖x'‖ = 1) (hy' : ‖y'‖ = 1)
    (hxi : x.im < 0) (hyi : y.im < 0) (hx'i : x'.im < 0) (hy'i : y'.im < 0)
    (hS : 0 < S) (hxy : x.re + y.re = S) (hxy' : x'.re + y'.re = S)
    (hratio : x.im / y.im = x'.im / y'.im) : x = x' ∧ y = y' := by
  have hc := (div_eq_div_iff (ne_of_lt hyi) (ne_of_lt hy'i)).mp hratio
  have hsquare : x.im ^ 2 * y'.im ^ 2 = x'.im ^ 2 * y.im ^ 2 := by
    have hh := congrArg (fun t : ℝ => t * t) hc
    nlinarith only [hh]
  have ex := unit_coordinate_equation hx
  have ey := unit_coordinate_equation hy
  have ex' := unit_coordinate_equation hx'
  have ey' := unit_coordinate_equation hy'
  have hsq : (1 - x.re ^ 2) * (1 - y'.re ^ 2) =
      (1 - x'.re ^ 2) * (1 - y.re ^ 2) := by
    rw [show 1 - x.re ^ 2 = x.im ^ 2 by linarith,
      show 1 - y'.re ^ 2 = y'.im ^ 2 by linarith,
      show 1 - x'.re ^ 2 = x'.im ^ 2 by linarith,
      show 1 - y.re ^ 2 = y.im ^ 2 by linarith]
    exact hsquare
  have hpos := ratio_cross_factor_positive (lower_unit_real_bounds hx hxi)
    (lower_unit_real_bounds hy hyi) (lower_unit_real_bounds hx' hx'i)
    (lower_unit_real_bounds hy' hy'i)
  have hfactor : S * (x.re - x'.re) * (2 - x.re * y'.re - x'.re * y.re) = 0 := by
    have hyr : y.re = S - x.re := by linarith
    have hy'r : y'.re = S - x'.re := by linarith
    rw [hyr, hy'r] at hsq ⊢
    nlinarith [hsq]
  have hrr : x.re = x'.re := by
    rcases mul_eq_zero.mp hfactor with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact False.elim ((ne_of_gt hS) h)
      · linarith
    · exact False.elim ((ne_of_gt hpos) h)
  exact ⟨lower_unit_eq_of_re_eq hx hx' hxi hx'i hrr,
    lower_unit_eq_of_re_eq hy hy' hyi hy'i (by linarith)⟩
 
/-- Coefficients of the actual product, pair, and dispersion vectors.
The two balance fields are the coordinate form of their zero vector sum.
Only coefficients of factors active at the limiting torus point may be nonzero. -/
structure ActiveCombination {N : ℕ} (x y : Fin N → ℂ) (S : ℝ) where
  productX : ℝ
  productY : ℝ
  pairX : Fin N → Fin N → ℝ
  pairY : Fin N → Fin N → ℝ
  dispersionWeight : Fin N → ℝ
  productX_nonneg : 0 ≤ productX
  productY_nonneg : 0 ≤ productY
  pairX_nonneg : ∀ i j, 0 ≤ pairX i j
  pairY_nonneg : ∀ i j, 0 ≤ pairY i j
  dispersion_nonneg : ∀ i, 0 ≤ dispersionWeight i
  productX_active : productX ≠ 0 → ∏ i, x i = 1
  productY_active : productY ≠ 0 → ∏ i, y i = 1
  pairX_active : ∀ i j, pairX i j ≠ 0 → i < j ∧ x i * x j = 1
  pairY_active : ∀ i j, pairY i j ≠ 0 → i < j ∧ y i * y j = 1
  dispersion_active : ∀ i, dispersionWeight i ≠ 0 → (x i).re + (y i).re = S
  balanceX : ∀ i, productX + (∑ j, (pairX i j + pairX j i)) +
    dispersionWeight i * (x i).im = 0
  balanceY : ∀ i, productY + (∑ j, (pairY i j + pairY j i)) +
    dispersionWeight i * (y i).im = 0

/-- The incident sum of nonnegative pair coefficients controls either incidence. -/
theorem pair_incident_le {N : ℕ} (P : Fin N → Fin N → ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (i j : Fin N) :
    P i j ≤ ∑ k, (P i k + P k i) := by
  exact le_trans (le_add_of_nonneg_right (hP j i))
    (Finset.single_le_sum (fun k _ => add_nonneg (hP i k) (hP k i)) (Finset.mem_univ j))

/-- Pair-vector coefficients vanish in every nonnegative zero combination. -/
theorem ActiveCombination.pairX_eq_zero {N : ℕ} {x y : Fin N → ℂ} {S : ℝ}
    (c : ActiveCombination x y S) (hx : ∀ i, ‖x i‖ = 1) (i j : Fin N) :
    c.pairX i j = 0 := by
  by_contra hn
  have hp : 0 < c.pairX i j := lt_of_le_of_ne (c.pairX_nonneg i j) (Ne.symm hn)
  have hi := pair_incident_le c.pairX c.pairX_nonneg i j
  have hj : c.pairX i j ≤ ∑ k, (c.pairX j k + c.pairX k j) := by
    exact le_trans (le_add_of_nonneg_left (c.pairX_nonneg j i))
      (Finset.single_le_sum (fun k _ => add_nonneg (c.pairX_nonneg j k)
        (c.pairX_nonneg k j)) (Finset.mem_univ i))
  have hneg (k : Fin N) (hk : 0 < ∑ l, (c.pairX k l + c.pairX l k)) :
      (x k).im < 0 := by
    have hb := c.balanceX k
    have hz := c.dispersion_nonneg k
    by_contra hh
    have hh' : 0 ≤ (x k).im := le_of_not_gt hh
    have := mul_nonneg hz hh'
    linarith [c.productX_nonneg]
  have hin := hneg i (lt_of_lt_of_le hp hi)
  have hjn := hneg j (lt_of_lt_of_le hp hj)
  have hop := reciprocal_unit_imaginary_sum (hx i) (c.pairX_active i j hn).2
  linarith

/-- Exchange of the two coordinate blocks preserves the coefficient equations. -/
def ActiveCombination.swap {N : ℕ} {x y : Fin N → ℂ} {S : ℝ}
    (c : ActiveCombination x y S) : ActiveCombination y x S where
  productX := c.productY
  productY := c.productX
  pairX := c.pairY
  pairY := c.pairX
  dispersionWeight := c.dispersionWeight
  productX_nonneg := c.productY_nonneg
  productY_nonneg := c.productX_nonneg
  pairX_nonneg := c.pairY_nonneg
  pairY_nonneg := c.pairX_nonneg
  dispersion_nonneg := c.dispersion_nonneg
  productX_active := c.productY_active
  productY_active := c.productX_active
  pairX_active := c.pairY_active
  pairY_active := c.pairX_active
  dispersion_active := fun i hi => by simpa [add_comm] using c.dispersion_active i hi
  balanceX := c.balanceY
  balanceY := c.balanceX

theorem ActiveCombination.pairY_eq_zero {N : ℕ} {x y : Fin N → ℂ} {S : ℝ}
    (c : ActiveCombination x y S) (hy : ∀ i, ‖y i‖ = 1) (i j : Fin N) :
    c.pairY i j = 0 := c.swap.pairX_eq_zero hy i j

/-- With pair vectors excluded, the x-coordinate balance has only two terms. -/
theorem ActiveCombination.productX_balance {N : ℕ} {x y : Fin N → ℂ} {S : ℝ}
    (c : ActiveCombination x y S) (hx : ∀ i, ‖x i‖ = 1) (i : Fin N) :
    c.productX + c.dispersionWeight i * (x i).im = 0 := by
  simpa [c.pairX_eq_zero hx] using c.balanceX i

theorem ActiveCombination.productY_balance {N : ℕ} {x y : Fin N → ℂ} {S : ℝ}
    (c : ActiveCombination x y S) (hy : ∀ i, ‖y i‖ = 1) (i : Fin N) :
    c.productY + c.dispersionWeight i * (y i).im = 0 :=
  c.swap.productX_balance hy i

/-- A positive x-product coefficient makes every dispersion coefficient positive
and puts every x coordinate in the strict lower half-plane. -/
theorem ActiveCombination.lowerX_of_productX_pos {N : ℕ} {x y : Fin N → ℂ} {S : ℝ}
    (c : ActiveCombination x y S) (hx : ∀ i, ‖x i‖ = 1) (hX : 0 < c.productX)
    (i : Fin N) : 0 < c.dispersionWeight i ∧ (x i).im < 0 := by
  have hb := c.productX_balance hx i
  have hz := c.dispersion_nonneg i
  have hzp : 0 < c.dispersionWeight i := by
    by_contra h
    have : c.dispersionWeight i = 0 := le_antisymm (le_of_not_gt h) hz
    rw [this, zero_mul, add_zero] at hb
    linarith
  refine ⟨hzp, ?_⟩
  by_contra h
  have := mul_nonneg hz (le_of_not_gt h)
  linarith

/-- The both-product case gives the same imaginary ratio at every coordinate. -/
theorem ActiveCombination.ratio_of_both_products {N : ℕ} {x y : Fin N → ℂ} {S : ℝ}
    (c : ActiveCombination x y S) (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (hX : 0 < c.productX) (hY : 0 < c.productY) (i : Fin N) :
    (x i).im / (y i).im = c.productX / c.productY := by
  have hl := c.lowerX_of_productX_pos hx hX i
  have hly := c.swap.lowerX_of_productX_pos hy hY i
  apply (div_eq_div_iff (ne_of_lt hly.2) (ne_of_gt hY)).mpr
  have h1 := c.productX_balance hx i
  have h2 := c.productY_balance hy i
  apply mul_left_cancel₀ (ne_of_gt hl.1)
  nlinarith [h1, h2]

/-- All coordinates coincide in the both-product case, as claimed in the manuscript. -/
theorem ActiveCombination.both_products_constant {N : ℕ} {x y : Fin N → ℂ} {S : ℝ}
    (c : ActiveCombination x y S) (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (hS : 0 < S) (hX : 0 < c.productX) (hY : 0 < c.productY) (i j : Fin N) :
    x i = x j ∧ y i = y j := by
  have hxi := c.lowerX_of_productX_pos hx hX i
  have hxj := c.lowerX_of_productX_pos hx hX j
  have hyi := c.swap.lowerX_of_productX_pos hy hY i
  have hyj := c.swap.lowerX_of_productX_pos hy hY j
  exact lower_dispersion_ratio_injective (hx i) (hy i) (hx j) (hy j)
    hxi.2 hyi.2 hxj.2 hyj.2 hS
    (c.dispersion_active i (ne_of_gt hxi.1)) (c.dispersion_active j (ne_of_gt hxj.1))
    ((c.ratio_of_both_products hx hy hX hY i).trans
      (c.ratio_of_both_products hx hy hX hY j).symm)

/-- A real point on the unit circle is one of its two real endpoints. -/
theorem unit_zero_imaginary {z : ℂ} (hz : ‖z‖ = 1) (hi : z.im = 0) :
    z = 1 ∨ z = -1 := by
  have he := unit_coordinate_equation hz
  rw [hi] at he
  have hr : z.re = 1 ∨ z.re = -1 := by
    have hp : (z.re - 1) * (z.re + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hp with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  rcases hr with h | h
  · left; apply Complex.ext <;> simp [h, hi]
  · right; apply Complex.ext <;> simp [h, hi]

/-- Active dispersion vectors cannot vanish on a level strictly between zero and two. -/
theorem positive_dispersion_vector_nonzero {x y : ℂ} {S : ℝ}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hS : 0 < S ∧ S < 2)
    (hxy : x.re + y.re = S) : ¬ (x.im = 0 ∧ y.im = 0) := by
  rintro ⟨hxi, hyi⟩
  rcases unit_zero_imaginary hx hxi with rfl | rfl <;>
    rcases unit_zero_imaginary hy hyi with rfl | rfl <;>
    norm_num at hxy <;> linarith [hS.1, hS.2]

/-- No nontrivial dispersion-only combination is possible. -/
theorem ActiveCombination.dispersion_eq_zero_of_products_zero {N : ℕ}
    {x y : Fin N → ℂ} {S : ℝ} (c : ActiveCombination x y S)
    (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1) (hS : 0 < S ∧ S < 2)
    (hX : c.productX = 0) (hY : c.productY = 0) (i : Fin N) :
    c.dispersionWeight i = 0 := by
  by_contra hn
  have hxi := c.productX_balance hx i
  have hyi := c.productY_balance hy i
  rw [hX, zero_add] at hxi
  rw [hY, zero_add] at hyi
  exact positive_dispersion_vector_nonzero (hx i) (hy i) hS (c.dispersion_active i hn)
    ⟨(mul_eq_zero.mp hxi).resolve_left hn, (mul_eq_zero.mp hyi).resolve_left hn⟩

/-- In the single x-product case the other coordinate is exactly +1.
The -1 case is excluded by the positive level, not omitted. -/
theorem ActiveCombination.one_product_other_eq_one {N : ℕ} {x y : Fin N → ℂ} {S : ℝ}
    (c : ActiveCombination x y S) (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (hS : 0 < S) (hX : 0 < c.productX) (hY : c.productY = 0) (i : Fin N) :
    y i = 1 := by
  have hl := c.lowerX_of_productX_pos hx hX i
  have hb := c.productY_balance hy i
  rw [hY, zero_add] at hb
  have hyi : (y i).im = 0 := (mul_eq_zero.mp hb).resolve_left (ne_of_gt hl.1)
  rcases unit_zero_imaginary (hy i) hyi with h | h
  · exact h
  · have hd := c.dispersion_active i (ne_of_gt hl.1)
    have hr := (lower_unit_real_bounds (hx i) hl.2).2
    rw [h] at hd
    norm_num at hd
    linarith

/-- The common real part in the remaining single-product case. -/
theorem ActiveCombination.one_product_real {N : ℕ} {x y : Fin N → ℂ} {S : ℝ}
    (c : ActiveCombination x y S) (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (hS : 0 < S) (hX : 0 < c.productX) (hY : c.productY = 0) (i : Fin N) :
    (x i).re = S - 1 := by
  have hl := c.lowerX_of_productX_pos hx hX i
  have hd := c.dispersion_active i (ne_of_gt hl.1)
  rw [c.one_product_other_eq_one hx hy hS hX hY i] at hd
  norm_num at hd
  linarith

/-- The frozen selected branch has precisely the real coordinate of the +1 exception. -/
theorem selected_branch_real {p : ℕ} {a b : ℤ}
    (ha : PrimeFamily.Admissible p a) (hb : PrimeFamily.Admissible p b) :
    (PrimeFamily.selectedBranch p a b).re = 2 * PrimeFamily.cosineAverage p a b - 1 := by
  have hc := PrimeFamily.cosineAverage_bounds ha hb
  unfold PrimeFamily.selectedBranch PrimeFamily.branchAngle
  rw [← Complex.ofReal_neg, Complex.exp_ofReal_mul_I_re, Real.cos_neg,
    Real.cos_arccos (by linarith) (by linarith)]

/-- The one-product case is impossible at the actual selected prime-family point. -/
theorem ActiveCombination.not_one_product_selected {N p : ℕ} {a b : ℤ}
    {x y : Fin N → ℂ} (hp : p.Prime)
    (ha : PrimeFamily.Admissible p a) (hb : PrimeFamily.Admissible p b)
    (c : ActiveCombination x y (2 * PrimeFamily.cosineAverage p a b))
    (hN : 0 < N) (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (hX : 0 < c.productX) (hY : c.productY = 0) : False := by
  have hS : 0 < 2 * PrimeFamily.cosineAverage p a b := by
    linarith [(PrimeFamily.cosineAverage_bounds ha hb).1]
  have hbranch := PrimeFamily.selectedBranch_unit_lower ha hb
  have heq (i : Fin N) : x i = PrimeFamily.selectedBranch p a b :=
    lower_unit_eq_of_re_eq (hx i) hbranch.1 (c.lowerX_of_productX_pos hx hX i).2 hbranch.2
      ((c.one_product_real hx hy hS hX hY i).trans (selected_branch_real ha hb).symm)
  have hpow : PrimeFamily.selectedBranch p a b ^ N = 1 := by
    simpa [heq] using c.productX_active (ne_of_gt hX)
  exact PrimeFamily.selectedBranch_not_isOfFinOrder hp ha hb
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨N, hN, hpow⟩)

/-- Every unit root of positive order has the exact integer-angle representation
accepted by the frozen prime-family uniqueness endpoint. -/
theorem root_eq_angleRoot {n : ℕ} (hn : n ≠ 0) {z : ℂ} (hz : z ^ n = 1) :
    ∃ l : ℤ, z = PrimeFamily.angleRoot n l := by
  let : NeZero n := ⟨hn⟩
  obtain ⟨j, _, hj⟩ := (Complex.isPrimitiveRoot_exp n hn).eq_pow_of_pow_eq_one hz
  refine ⟨j, ?_⟩
  rw [← hj, ← Complex.exp_nat_mul]
  unfold PrimeFamily.angleRoot PrimeFamily.angle
  push_cast
  congr 1
  ring

/-- The two selected lower roots, in manuscript angle notation. -/
def selectedLowerRoot (p : ℕ) (a : ℤ) : ℂ :=
  Complex.exp (-(PrimeFamily.angle p a : ℂ) * Complex.I)

theorem selected_lower_root_unit_lower {p : ℕ} {a : ℤ}
    (ha : PrimeFamily.Admissible p a) :
    ‖selectedLowerRoot p a‖ = 1 ∧ (selectedLowerRoot p a).im < 0 := by
  constructor
  · simpa [selectedLowerRoot] using Complex.norm_exp_ofReal_mul_I (-PrimeFamily.angle p a)
  · rw [selectedLowerRoot, ← Complex.ofReal_neg, Complex.exp_ofReal_mul_I_im, Real.sin_neg]
    have hpi : PrimeFamily.angle p a < Real.pi := by linarith [ha.2, Real.pi_pos]
    exact neg_neg_of_pos (Real.sin_pos_of_pos_of_lt_pi ha.1 hpi)

theorem selected_lower_root_real (p : ℕ) (a : ℤ) :
    (selectedLowerRoot p a).re = Real.cos (PrimeFamily.angle p a) := by
  rw [selectedLowerRoot, ← Complex.ofReal_neg, Complex.exp_ofReal_mul_I_re, Real.cos_neg]

/-- The both-product case at N=2p consists of exactly the two ordered lower charts. -/
theorem ActiveCombination.both_products_selected {p : ℕ} {a b : ℤ}
    {x y : Fin (2*p) → ℂ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (ha : PrimeFamily.Admissible p a) (hb : PrimeFamily.Admissible p b)
    (c : ActiveCombination x y (2 * PrimeFamily.cosineAverage p a b))
    (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (hX : 0 < c.productX) (hY : 0 < c.productY) :
    ((∀ i, x i = selectedLowerRoot p a) ∧ (∀ i, y i = selectedLowerRoot p b)) ∨
    ((∀ i, x i = selectedLowerRoot p b) ∧ (∀ i, y i = selectedLowerRoot p a)) := by
  have hn : 0 < 2*p := by omega
  let i : Fin (2*p) := ⟨0, hn⟩
  have hS : 0 < 2 * PrimeFamily.cosineAverage p a b := by
    linarith [(PrimeFamily.cosineAverage_bounds ha hb).1]
  have hconst := c.both_products_constant hx hy hS hX hY
  have hxp : x i ^ (2*p) = 1 := by
    calc
      _ = ∏ _j : Fin (2*p), x i := by simp
      _ = ∏ j, x j := Finset.prod_congr rfl (fun j _ => (hconst j i).1.symm)
      _ = 1 := c.productX_active (ne_of_gt hX)
  have hyp : y i ^ (2*p) = 1 := by
    calc
      _ = ∏ _j : Fin (2*p), y i := by simp
      _ = ∏ j, y j := Finset.prod_congr rfl (fun j _ => (hconst j i).2.symm)
      _ = 1 := c.productY_active (ne_of_gt hY)
  obtain ⟨l, hl⟩ := root_eq_angleRoot (ne_of_gt hn) hxp
  obtain ⟨m, hm⟩ := root_eq_angleRoot (ne_of_gt hn) hyp
  have hxr : (x i).re = Real.cos (PrimeFamily.angle (2*p) l) := by
    rw [hl, PrimeFamily.angleRoot, Complex.exp_ofReal_mul_I_re]
  have hyr : (y i).re = Real.cos (PrimeFamily.angle (2*p) m) := by
    rw [hm, PrimeFamily.angleRoot, Complex.exp_ofReal_mul_I_re]
  have hd := c.dispersion_active i (ne_of_gt (c.lowerX_of_productX_pos hx hX i).1)
  have hrep : PrimeFamily.selectedPoint p a b + (PrimeFamily.selectedPoint p a b)⁻¹ =
      (Real.cos (PrimeFamily.angle (2*p) l) : ℂ) +
      (Real.cos (PrimeFamily.angle (2*p) m) : ℂ) := by
    rw [PrimeFamily.selectedPoint_relation ha hb, ← hxr, ← hyr]
    exact_mod_cast hd.symm
  have hrx {j : ℤ} (hj : PrimeFamily.Admissible p j)
      (hreal : (x i).re = Real.cos (PrimeFamily.angle p j)) :
      ∀ k, x k = selectedLowerRoot p j := by
    intro k
    rw [(hconst k i).1]
    exact lower_unit_eq_of_re_eq (hx i) (selected_lower_root_unit_lower hj).1
      (c.lowerX_of_productX_pos hx hX i).2 (selected_lower_root_unit_lower hj).2
      (hreal.trans (selected_lower_root_real p j).symm)
  have hry {j : ℤ} (hj : PrimeFamily.Admissible p j)
      (hreal : (y i).re = Real.cos (PrimeFamily.angle p j)) :
      ∀ k, y k = selectedLowerRoot p j := by
    intro k
    rw [(hconst k i).2]
    exact lower_unit_eq_of_re_eq (hy i) (selected_lower_root_unit_lower hj).1
      (c.swap.lowerX_of_productX_pos hy hY i).2 (selected_lower_root_unit_lower hj).2
      (hreal.trans (selected_lower_root_real p j).symm)
  rcases PrimeFamily.unique_cosine_pair hp hp11 ha hb l m hrep with h | h
  · exact Or.inl ⟨hrx ha (hxr.trans h.1), hry hb (hyr.trans h.2)⟩
  · exact Or.inr ⟨hrx hb (hxr.trans h.1), hry ha (hyr.trans h.2)⟩

/-- Exactly the two ordered bad double-torus configurations in FIRST. -/
def selectedBadConfiguration {p : ℕ} (a b : ℤ) (x y : Fin (2*p) → ℂ) : Prop :=
  ((∀ i, x i = selectedLowerRoot p a) ∧ (∀ i, y i = selectedLowerRoot p b)) ∨
  ((∀ i, x i = selectedLowerRoot p b) ∧ (∀ i, y i = selectedLowerRoot p a))

/-- Exhaustive algebraic classification: off those two configurations every
nonnegative active zero combination has all coefficients zero. -/
theorem ActiveCombination.zero_off_selected {p : ℕ} {a b : ℤ}
    {x y : Fin (2*p) → ℂ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (ha : PrimeFamily.Admissible p a) (hb : PrimeFamily.Admissible p b)
    (c : ActiveCombination x y (2 * PrimeFamily.cosineAverage p a b))
    (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (hgood : ¬ selectedBadConfiguration a b x y) :
    c.productX = 0 ∧ c.productY = 0 ∧
      (∀ i j, c.pairX i j = 0) ∧ (∀ i j, c.pairY i j = 0) ∧
      (∀ i, c.dispersionWeight i = 0) := by
  have hn : 0 < 2*p := by omega
  have hX : c.productX = 0 := by
    by_contra h
    have hxp : 0 < c.productX := lt_of_le_of_ne c.productX_nonneg (Ne.symm h)
    by_cases hY : c.productY = 0
    · exact c.not_one_product_selected hp ha hb hn hx hy hxp hY
    · have hyp : 0 < c.productY := lt_of_le_of_ne c.productY_nonneg (Ne.symm hY)
      exact hgood (c.both_products_selected hp hp11 ha hb hx hy hxp hyp)
  have hY : c.productY = 0 := by
    by_contra h
    exact c.swap.not_one_product_selected hp ha hb hn hy hx
      (lt_of_le_of_ne c.productY_nonneg (Ne.symm h)) hX
  have hS : 0 < 2 * PrimeFamily.cosineAverage p a b ∧
      2 * PrimeFamily.cosineAverage p a b < 2 := by
    have h := PrimeFamily.cosineAverage_bounds ha hb
    constructor <;> linarith
  exact ⟨hX, hY, c.pairX_eq_zero hx, c.pairY_eq_zero hy,
    c.dispersion_eq_zero_of_products_zero hx hy hS hX hY⟩

end
end IsingBulk.First
