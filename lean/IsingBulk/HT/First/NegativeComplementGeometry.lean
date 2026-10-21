import IsingBulk.HT.First.NegativeActiveGeometry
import IsingBulk.HT.First.OddComplementGeometry

/-! Actual negative-family order-p complement classification. The same two
lower-torus configurations occur, and the actual −1 exceptional branch is
excluded by the new trace theorem. All nonstationary infrastructure is reused. -/
namespace IsingBulk.HT.First
noncomputable section
open Complex Set IsingBulk.First
open scoped BigOperators

theorem negative_selected_lower_root_unit_lower {p : ℕ} {a : ℤ}
    (ha : NegativeAdmissible p a) :
    ‖selectedLowerRoot p a‖=1 ∧ (selectedLowerRoot p a).im<0 := by
  constructor
  · simpa [selectedLowerRoot] using
      Complex.norm_exp_ofReal_mul_I (-PrimeFamily.angle p a)
  · rw [selectedLowerRoot,← Complex.ofReal_neg,Complex.exp_ofReal_mul_I_im,Real.sin_neg]
    exact neg_neg_of_pos (Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos,ha.1]) ha.2)

/-- The both-product case at N=p consists of exactly the two ordered lower charts. -/
theorem negative_both_products_selected_odd {p : ℕ} {a b : ℤ}
    {x y : Fin p → ℂ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b)
    (c : ActiveCombination x y (2 * PrimeFamily.cosineAverage p a b))
    (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (hX : 0 < c.productX) (hY : 0 < c.productY) :
    ((∀ i, x i = selectedLowerRoot p a) ∧ (∀ i, y i = selectedLowerRoot p b)) ∨
    ((∀ i, x i = selectedLowerRoot p b) ∧ (∀ i, y i = selectedLowerRoot p a)) := by
  have hn : 0 < p := by omega
  let i : Fin p := ⟨0, hn⟩
  have hS : 2 * PrimeFamily.cosineAverage p a b < 0 := by
    linarith [(negative_cosineAverage_bounds ha hb).2]
  have hconst := both_products_constant_of_level_ne_zero c hx hy (ne_of_lt hS) hX hY
  have hxp : x i ^ p = 1 := by
    calc
      _ = ∏ _j : Fin p, x i := by simp
      _ = ∏ j, x j := Finset.prod_congr rfl (fun j _ => (hconst j i).1.symm)
      _ = 1 := c.productX_active (ne_of_gt hX)
  have hyp : y i ^ p = 1 := by
    calc
      _ = ∏ _j : Fin p, y i := by simp
      _ = ∏ j, y j := Finset.prod_congr rfl (fun j _ => (hconst j i).2.symm)
      _ = 1 := c.productY_active (ne_of_gt hY)
  obtain ⟨l, hl⟩ := root_eq_angleRoot (ne_of_gt hn) hxp
  obtain ⟨m, hm⟩ := root_eq_angleRoot (ne_of_gt hn) hyp
  have hxr : (x i).re = Real.cos (PrimeFamily.angle p l) := by
    rw [hl, PrimeFamily.angleRoot, Complex.exp_ofReal_mul_I_re]
  have hyr : (y i).re = Real.cos (PrimeFamily.angle p m) := by
    rw [hm, PrimeFamily.angleRoot, Complex.exp_ofReal_mul_I_re]
  have hd := c.dispersion_active i (ne_of_gt (c.lowerX_of_productX_pos hx hX i).1)
  have hrep : PrimeFamily.selectedPoint p a b + (PrimeFamily.selectedPoint p a b)⁻¹ =
      (Real.cos (PrimeFamily.angle p l) : ℂ) +
      (Real.cos (PrimeFamily.angle p m) : ℂ) := by
    rw [negative_selectedPoint_relation ha hb, ← hxr, ← hyr]
    exact_mod_cast hd.symm
  have hrx {j : ℤ} (hj : NegativeAdmissible p j)
      (hreal : (x i).re = Real.cos (PrimeFamily.angle p j)) :
      ∀ k, x k = selectedLowerRoot p j := by
    intro k
    rw [(hconst k i).1]
    exact lower_unit_eq_of_re_eq (hx i) (negative_selected_lower_root_unit_lower hj).1
      (c.lowerX_of_productX_pos hx hX i).2 (negative_selected_lower_root_unit_lower hj).2
      (hreal.trans (selected_lower_root_real p j).symm)
  have hry {j : ℤ} (hj : NegativeAdmissible p j)
      (hreal : (y i).re = Real.cos (PrimeFamily.angle p j)) :
      ∀ k, y k = selectedLowerRoot p j := by
    intro k
    rw [(hconst k i).2]
    exact lower_unit_eq_of_re_eq (hy i) (negative_selected_lower_root_unit_lower hj).1
      (c.swap.lowerX_of_productX_pos hy hY i).2 (negative_selected_lower_root_unit_lower hj).2
      (hreal.trans (selected_lower_root_real p j).symm)
  rcases negative_unique_prime_cosine_pair hp hp11 ha hb l m hrep with h | h
  · exact Or.inl ⟨hrx ha (hxr.trans h.1), hry hb (hyr.trans h.2)⟩
  · exact Or.inr ⟨hrx hb (hxr.trans h.1), hry ha (hyr.trans h.2)⟩

/-- Exhaustive algebraic classification: off those two configurations every
nonnegative active zero combination has all coefficients zero. -/
theorem negative_zero_off_selected_odd {p : ℕ} {a b : ℤ}
    {x y : Fin p → ℂ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b)
    (c : ActiveCombination x y (2 * PrimeFamily.cosineAverage p a b))
    (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (hgood : ¬ oddSelectedBadConfiguration a b x y) :
    c.productX = 0 ∧ c.productY = 0 ∧
      (∀ i j, c.pairX i j = 0) ∧ (∀ i j, c.pairY i j = 0) ∧
      (∀ i, c.dispersionWeight i = 0) := by
  have hn : 0 < p := by omega
  have hX : c.productX = 0 := by
    by_contra h
    have hxp : 0 < c.productX := lt_of_le_of_ne c.productX_nonneg (Ne.symm h)
    by_cases hY : c.productY = 0
    · exact negative_not_one_product_selected hp hp11 ha hb c hn hx hy hxp hY
    · have hyp : 0 < c.productY := lt_of_le_of_ne c.productY_nonneg (Ne.symm hY)
      exact hgood (negative_both_products_selected_odd hp hp11 ha hb c hx hy hxp hyp)
  have hY : c.productY = 0 := by
    by_contra h
    exact negative_not_one_product_selected hp hp11 ha hb c.swap hn hy hx
      (lt_of_le_of_ne c.productY_nonneg (Ne.symm h)) hX
  have hS : -2 < 2 * PrimeFamily.cosineAverage p a b ∧
      2 * PrimeFamily.cosineAverage p a b < 0 := by
    have h := negative_cosineAverage_bounds ha hb
    constructor <;> linarith
  exact ⟨hX, hY, c.pairX_eq_zero hx, c.pairY_eq_zero hy,
    negative_dispersion_eq_zero_of_products_zero c hx hy hS hX hY⟩

/-- Every coefficient of a genuine nonnegative active vector zero sum is zero
away from the two selected configurations. -/
theorem negative_odd_active_vector_zero_coefficients {p : ℕ} {a b : ℤ}
    {x y : Fin p → ℂ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b)
    (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (hgood : ¬ oddSelectedBadConfiguration a b x y)
    (w : SingularFactorIndex p → ℝ) (hw : ∀ f, 0 ≤ w f)
    (hact : ∀ f, w f ≠ 0 → singularFactorActive x y (2 * PrimeFamily.cosineAverage p a b) f)
    (hsum : ∑ f, w f • singularFactorVector x y f = 0) : ∀ f, w f = 0 := by
  let c := activeCombinationOfVectorSum w hw hact hsum
  have h := negative_zero_off_selected_odd hp hp11 ha hb c hx hy hgood
  rintro (b | (⟨b, i, j⟩ | i))
  · cases b
    · exact h.1
    · exact h.2.1
  · cases b
    · exact h.2.2.1 i j
    · exact h.2.2.2.1 i j
  · exact h.2.2.2.2 i

/-- Actual active vectors have no zero convex combination off the two charts. -/
theorem negative_odd_zero_not_mem_active_convexHull {p : ℕ} {a b : ℤ}
    {x y : Fin p → ℂ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b)
    (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (hgood : ¬ oddSelectedBadConfiguration a b x y) :
    (0 : DoubleAngularVector p) ∉
      convexHull ℝ (activeSingularVectorSet x y (2 * PrimeFamily.cosineAverage p a b)) := by
  classical
  let P := singularFactorActive x y (2 * PrimeFamily.cosineAverage p a b)
  change (0 : DoubleAngularVector p) ∉
    convexHull ℝ (range (fun f : {f : SingularFactorIndex p // P f} =>
      singularFactorVector x y f.val))
  apply zero_not_mem_convexHull_range_of_nonnegative_relation
  intro w hw hsum
  let W : SingularFactorIndex p → ℝ := fun f => if hf : P f then w ⟨f, hf⟩ else 0
  have hW : ∀ f, 0 ≤ W f := by
    intro f
    by_cases hf : P f
    · simpa [W, hf] using hw ⟨f, hf⟩
    · simp [W, hf]
  have hact : ∀ f, W f ≠ 0 → P f := by
    intro f hf
    by_contra hnf
    exact hf (by simp [W, hnf])
  have hv : ∑ f, W f • singularFactorVector x y f = 0 := by
    rw [← Fintype.sum_subtype_add_sum_subtype P]
    have h₁ : (∑ f : {f : SingularFactorIndex p // P f},
        W f.val • singularFactorVector x y f.val) =
        ∑ f, w f • singularFactorVector x y f.val := by
      apply Finset.sum_congr rfl
      intro f _
      simp [W, f.property]
    have h₂ : (∑ f : {f : SingularFactorIndex p // ¬P f},
        W f.val • singularFactorVector x y f.val) = 0 := by
      apply Finset.sum_eq_zero
      intro f _
      simp [W, f.property]
    rw [h₁, h₂, add_zero]
    exact hsum
  have hz := negative_odd_active_vector_zero_coefficients hp hp11 ha hb hx hy hgood W hW hact hv
  intro f
  simpa [W, f.property] using hz f.val

/-- A positive separating functional for every active source vector, obtained
from the proved classification rather than inserted as a setup hypothesis. -/
theorem negative_odd_selected_active_separating_functional {p : ℕ} {a b : ℤ}
    {x y : Fin p → ℂ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b)
    (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (hgood : ¬ oddSelectedBadConfiguration a b x y) :
    ∃ (f : StrongDual ℝ (DoubleAngularVector p)) (δ : ℝ),
      0 < δ ∧ ∀ i, singularFactorActive x y (2 * PrimeFamily.cosineAverage p a b) i →
        δ < f (singularFactorVector x y i) := by
  classical
  let V := activeSingularVectorSet x y (2 * PrimeFamily.cosineAverage p a b)
  have hfin : V.Finite := Set.finite_range _
  have hsep := geometric_hahn_banach_point_closed (convex_convexHull ℝ V)
    (hfin.isCompact_convexHull ℝ).isClosed
    (negative_odd_zero_not_mem_active_convexHull hp hp11 ha hb hx hy hgood)
  obtain ⟨f, δ, hδ, hf⟩ := hsep
  refine ⟨f, δ, by simpa using hδ, ?_⟩
  intro i hi
  exact hf _ (subset_convexHull ℝ V ⟨⟨i, hi⟩, rfl⟩)


end
end IsingBulk.HT.First
