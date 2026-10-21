import IsingBulk.HT.First.NegativeActiveGeometry
import IsingBulk.First.NonNickelGeometry

/-! Negative selected-family lower-order geometry. A single product is
excluded by the actual exceptional-branch nonresonance; both products force a
Nickel representation. Neither case is discarded by a positive-level premise. -/
namespace IsingBulk.HT.First
noncomputable section
open Complex Set IsingBulk.First
open scoped BigOperators

theorem nickel_of_both_products_pos {N : ℕ} (hN : 0 < N)
    {x y : Fin N → ℂ} {S : ℝ} {s₀ : ℂ}
    (c : ActiveCombination x y S)
    (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (hS : S ≠ 0) (hs₀ : ‖s₀‖ = 1) (hrel : s₀+s₀⁻¹ = (S:ℂ))
    (hX : 0 < c.productX) (hY : 0 < c.productY) : PrimeFamily.NickelAt s₀ N := by
  let i : Fin N := ⟨0,hN⟩
  have hconst := both_products_constant_of_level_ne_zero c hx hy hS hX hY
  have hxp : x i ^ N = 1 := by
    calc
      _ = ∏ _j : Fin N, x i := by simp
      _ = ∏ j, x j := Finset.prod_congr rfl (fun j _ => (hconst j i).1.symm)
      _ = 1 := c.productX_active (ne_of_gt hX)
  have hyp : y i ^ N = 1 := by
    calc
      _ = ∏ _j : Fin N, y i := by simp
      _ = ∏ j, y j := Finset.prod_congr rfl (fun j _ => (hconst j i).2.symm)
      _ = 1 := c.productY_active (ne_of_gt hY)
  obtain ⟨l,hl⟩ := root_eq_angleRoot (ne_of_gt hN) hxp
  obtain ⟨m,hm⟩ := root_eq_angleRoot (ne_of_gt hN) hyp
  refine ⟨hs₀,l,m,?_⟩
  have hd := c.dispersion_active i (ne_of_gt (c.lowerX_of_productX_pos hx hX i).1)
  simp only [hl,hm,PrimeFamily.angleRoot,Complex.exp_ofReal_mul_I_re] at hd
  rw [hrel]
  exact_mod_cast hd.symm

theorem negative_zero_of_nonNickel {N p : ℕ} (hN : 0 < N)
    {a b : ℤ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b)
    {x y : Fin N → ℂ}
    (c : ActiveCombination x y (2*PrimeFamily.cosineAverage p a b))
    (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (hn : ¬ PrimeFamily.NickelAt (PrimeFamily.selectedPoint p a b) N) :
    c.productX = 0 ∧ c.productY = 0 ∧
      (∀ i j, c.pairX i j = 0) ∧ (∀ i j, c.pairY i j = 0) ∧
      (∀ i, c.dispersionWeight i = 0) := by
  have hlevel : -2 < 2*PrimeFamily.cosineAverage p a b ∧
      2*PrimeFamily.cosineAverage p a b < 0 := by
    have hc := negative_cosineAverage_bounds ha hb
    constructor <;> linarith
  have hrel : PrimeFamily.selectedPoint p a b+(PrimeFamily.selectedPoint p a b)⁻¹ =
      ((2*PrimeFamily.cosineAverage p a b:ℝ):ℂ) := by
    simpa only [Complex.ofReal_mul,Complex.ofReal_ofNat] using negative_selectedPoint_relation ha hb
  have hX : c.productX = 0 := by
    by_contra h
    have hxp := lt_of_le_of_ne c.productX_nonneg (Ne.symm h)
    by_cases hY : c.productY = 0
    · exact negative_not_one_product_selected hp hp11 ha hb c hN hx hy hxp hY
    · exact hn (nickel_of_both_products_pos hN c hx hy (ne_of_lt hlevel.2)
        (Complex.norm_exp_ofReal_mul_I _) hrel hxp
        (lt_of_le_of_ne c.productY_nonneg (Ne.symm hY)))
  have hY : c.productY = 0 := by
    by_contra h
    exact negative_not_one_product_selected hp hp11 ha hb c.swap hN hy hx
      (lt_of_le_of_ne c.productY_nonneg (Ne.symm h)) hX
  exact ⟨hX,hY,c.pairX_eq_zero hx,c.pairY_eq_zero hy,
    negative_dispersion_eq_zero_of_products_zero c hx hy hlevel hX hY⟩

theorem negative_nonNickel_active_separated {N p : ℕ} (hN : 0 < N)
    {a b : ℤ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (ha : NegativeAdmissible p a) (hb : NegativeAdmissible p b)
    {x y : Fin N → ℂ}
    (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (hn : ¬ PrimeFamily.NickelAt (PrimeFamily.selectedPoint p a b) N) : ActiveSourceSeparated x y (2*PrimeFamily.cosineAverage p a b) := by
  classical
  let P := singularFactorActive x y (2*PrimeFamily.cosineAverage p a b)
  let V := activeSingularVectorSet x y (2*PrimeFamily.cosineAverage p a b)
  have hz : (0 : DoubleAngularVector N) ∉ convexHull ℝ V := by
    change (0 : DoubleAngularVector N) ∉ convexHull ℝ
      (range (fun f : {f : SingularFactorIndex N // P f} => singularFactorVector x y f.val))
    apply zero_not_mem_convexHull_range_of_nonnegative_relation
    intro w hw hsum
    let W : SingularFactorIndex N → ℝ := fun f => if hf : P f then w ⟨f,hf⟩ else 0
    have hW : ∀ f, 0 ≤ W f := by
      intro f
      by_cases hf : P f
      · simpa [W,hf] using hw ⟨f,hf⟩
      · simp [W,hf]
    have hact : ∀ f, W f ≠ 0 → P f := by
      intro f hf
      by_contra hnf
      exact hf (by simp [W,hnf])
    have hv : ∑ f, W f • singularFactorVector x y f = 0 := by
      rw [← Fintype.sum_subtype_add_sum_subtype P]
      have h₁ : (∑ f : {f : SingularFactorIndex N // P f},
          W f.val • singularFactorVector x y f.val) =
          ∑ f, w f • singularFactorVector x y f.val := by
        apply Finset.sum_congr rfl
        intro f _
        simp [W,f.property]
      have h₂ : (∑ f : {f : SingularFactorIndex N // ¬ P f},
          W f.val • singularFactorVector x y f.val) = 0 := by
        apply Finset.sum_eq_zero
        intro f _
        simp [W,f.property]
      rw [h₁,h₂,add_zero]
      exact hsum
    let c := activeCombinationOfVectorSum W hW hact hv
    have hc := negative_zero_of_nonNickel hN hp hp11 ha hb c hx hy hn
    have hzero : ∀ f, W f = 0 := by
      rintro (b | (⟨b,i,j⟩ | i))
      · cases b
        · exact hc.1
        · exact hc.2.1
      · cases b
        · exact hc.2.2.1 i j
        · exact hc.2.2.2.1 i j
      · exact hc.2.2.2.2 i
    intro f
    simpa [W,f.property] using hzero f.val
  have hfin : V.Finite := Set.finite_range _
  obtain ⟨f,δ,hδ,hf⟩ := geometric_hahn_banach_point_closed (convex_convexHull ℝ V)
    (hfin.isCompact_convexHull ℝ).isClosed hz
  refine ⟨f,δ,by simpa using hδ,?_⟩
  intro i hi
  exact hf _ (subset_convexHull ℝ V ⟨⟨i,hi⟩,rfl⟩)


end
end IsingBulk.HT.First
