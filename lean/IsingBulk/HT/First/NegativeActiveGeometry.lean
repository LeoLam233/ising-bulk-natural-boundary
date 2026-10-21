import IsingBulk.First.ComplementVectors
import IsingBulk.HT.First.NegativePrimeOrder

/-! Actual negative-level active-vector geometry. The only changes in the
source classification are S≠0 instead of S>0 in ratio injectivity, and the
exceptional endpoint −1 instead of +1. The latter is excluded by the proved
negative-branch trace theorem, rather than a positive-level shortcut. -/
namespace IsingBulk.HT.First
noncomputable section
open Complex IsingBulk.First
open scoped BigOperators

theorem lower_dispersion_ratio_injective_of_ne_zero {x y x' y' : ℂ} {S : ℝ}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hx' : ‖x'‖ = 1) (hy' : ‖y'‖ = 1)
    (hxi : x.im < 0) (hyi : y.im < 0) (hx'i : x'.im < 0) (hy'i : y'.im < 0)
    (hS : S ≠ 0) (hxy : x.re + y.re = S) (hxy' : x'.re + y'.re = S)
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
      · exact False.elim (hS h)
      · linarith
    · exact False.elim ((ne_of_gt hpos) h)
  exact ⟨lower_unit_eq_of_re_eq hx hx' hxi hx'i hrr,
    lower_unit_eq_of_re_eq hy hy' hyi hy'i (by linarith)⟩
 

theorem both_products_constant_of_level_ne_zero {N : ℕ} {x y : Fin N → ℂ} {S : ℝ}
    (c : ActiveCombination x y S) (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (hS : S ≠ 0) (hX : 0 < c.productX) (hY : 0 < c.productY) (i j : Fin N) :
    x i = x j ∧ y i = y j := by
  have hxi := c.lowerX_of_productX_pos hx hX i
  have hxj := c.lowerX_of_productX_pos hx hX j
  have hyi := c.swap.lowerX_of_productX_pos hy hY i
  have hyj := c.swap.lowerX_of_productX_pos hy hY j
  exact lower_dispersion_ratio_injective_of_ne_zero (hx i) (hy i) (hx j) (hy j)
    hxi.2 hyi.2 hxj.2 hyj.2 hS
    (c.dispersion_active i (ne_of_gt hxi.1)) (c.dispersion_active j (ne_of_gt hxj.1))
    ((c.ratio_of_both_products hx hy hX hY i).trans
      (c.ratio_of_both_products hx hy hX hY j).symm)


theorem negative_dispersion_vector_nonzero {x y : ℂ} {S : ℝ}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hS : -2 < S ∧ S < 0)
    (hxy : x.re + y.re = S) : ¬ (x.im = 0 ∧ y.im = 0) := by
  rintro ⟨hxi, hyi⟩
  rcases unit_zero_imaginary hx hxi with rfl | rfl <;>
    rcases unit_zero_imaginary hy hyi with rfl | rfl <;>
    norm_num at hxy <;> linarith [hS.1, hS.2]

/-- No nontrivial dispersion-only combination is possible. -/
theorem negative_dispersion_eq_zero_of_products_zero {N : ℕ}
    {x y : Fin N → ℂ} {S : ℝ} (c : ActiveCombination x y S)
    (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1) (hS : -2 < S ∧ S < 0)
    (hX : c.productX = 0) (hY : c.productY = 0) (i : Fin N) :
    c.dispersionWeight i = 0 := by
  by_contra hn
  have hxi := c.productX_balance hx i
  have hyi := c.productY_balance hy i
  rw [hX, zero_add] at hxi
  rw [hY, zero_add] at hyi
  exact negative_dispersion_vector_nonzero (hx i) (hy i) hS (c.dispersion_active i hn)
    ⟨(mul_eq_zero.mp hxi).resolve_left hn, (mul_eq_zero.mp hyi).resolve_left hn⟩


theorem negative_one_product_other_eq_neg_one {N : ℕ} {x y : Fin N → ℂ} {S : ℝ}
    (c : ActiveCombination x y S) (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (hS : S < 0) (hX : 0 < c.productX) (hY : c.productY = 0) (i : Fin N) :
    y i = -1 := by
  have hl := c.lowerX_of_productX_pos hx hX i
  have hb := c.productY_balance hy i
  rw [hY, zero_add] at hb
  have hyi : (y i).im = 0 := (mul_eq_zero.mp hb).resolve_left (ne_of_gt hl.1)
  rcases unit_zero_imaginary (hy i) hyi with h | h
  · have hd := c.dispersion_active i (ne_of_gt hl.1)
    have hr := (lower_unit_real_bounds (hx i) hl.2).1
    rw [h] at hd
    norm_num at hd
    linarith
  · exact h

/-- The common real part in the remaining single-product case. -/
theorem negative_one_product_real {N : ℕ} {x y : Fin N → ℂ} {S : ℝ}
    (c : ActiveCombination x y S) (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (hS : S < 0) (hX : 0 < c.productX) (hY : c.productY = 0) (i : Fin N) :
    (x i).re = S + 1 := by
  have hl := c.lowerX_of_productX_pos hx hX i
  have hd := c.dispersion_active i (ne_of_gt hl.1)
  rw [negative_one_product_other_eq_neg_one c hx hy hS hX hY i] at hd
  norm_num at hd
  linarith


theorem negative_selected_branch_real {p : ℕ} {a b : ℤ}
    (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b) :
    (negativeSelectedBranch p a b).re = 2 * PrimeFamily.cosineAverage p a b + 1 := by
  have hc := negative_cosineAverage_bounds ha hb
  unfold negativeSelectedBranch 
  rw [← Complex.ofReal_neg, Complex.exp_ofReal_mul_I_re, Real.cos_neg,
    Real.cos_arccos (by linarith) (by linarith)]

/-- The one-product case is impossible at the actual selected prime-family point. -/
theorem negative_not_one_product_selected {N p : ℕ} {a b : ℤ}
    {x y : Fin N → ℂ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b)
    (c : ActiveCombination x y (2 * PrimeFamily.cosineAverage p a b))
    (hN : 0 < N) (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (hX : 0 < c.productX) (hY : c.productY = 0) : False := by
  have hS : 2 * PrimeFamily.cosineAverage p a b < 0 := by
    linarith [(negative_cosineAverage_bounds ha hb).2]
  have hbranch := negativeSelectedBranch_unit_lower ha hb
  have heq (i : Fin N) : x i = negativeSelectedBranch p a b :=
    lower_unit_eq_of_re_eq (hx i) hbranch.1 (c.lowerX_of_productX_pos hx hX i).2 hbranch.2
      ((negative_one_product_real c hx hy hS hX hY i).trans (negative_selected_branch_real ha hb).symm)
  have hpow : negativeSelectedBranch p a b ^ N = 1 := by
    simpa [heq] using c.productX_active (ne_of_gt hX)
  exact negativeSelectedBranch_not_isOfFinOrder hp hp11 ha hb
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨N, hN, hpow⟩)


end
end IsingBulk.HT.First
