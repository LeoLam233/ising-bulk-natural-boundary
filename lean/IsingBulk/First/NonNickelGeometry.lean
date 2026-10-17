import IsingBulk.First.ComplementVectors

/-! The nonstationary classification at any non-Nickel point of positive
dispersion level. In particular it applies to every lower selected even order.
No published fixed-order smoothness input occurs in this module. -/
namespace IsingBulk.First
noncomputable section
open scoped BigOperators
open Set

/-- A positive product coefficient forces a Nickel equation, including the
single-product case: there the other coordinates are all +1. -/
theorem ActiveCombination.nickel_of_productX_pos {N : ℕ} (hN : 0 < N)
    {x y : Fin N → ℂ} {S : ℝ} {s₀ : ℂ}
    (c : ActiveCombination x y S)
    (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (hS : 0 < S) (hs₀ : ‖s₀‖ = 1) (hrel : s₀+s₀⁻¹ = (S:ℂ))
    (hX : 0 < c.productX) : PrimeFamily.NickelAt s₀ N := by
  let i : Fin N := ⟨0,hN⟩
  have hconst : ∀ j, x j = x i ∧ y j = y i := by
    intro j
    by_cases hY : c.productY = 0
    · have hxi := c.lowerX_of_productX_pos hx hX i
      have hxj := c.lowerX_of_productX_pos hx hX j
      refine ⟨lower_unit_eq_of_re_eq (hx j) (hx i) hxj.2 hxi.2 ?_, ?_⟩
      · rw [c.one_product_real hx hy hS hX hY j,
          c.one_product_real hx hy hS hX hY i]
      · rw [c.one_product_other_eq_one hx hy hS hX hY j,
          c.one_product_other_eq_one hx hy hS hX hY i]
    · exact c.both_products_constant hx hy hS hX
        (lt_of_le_of_ne c.productY_nonneg (Ne.symm hY)) j i
  have hxp : x i ^ N = 1 := by
    calc
      _ = ∏ _j : Fin N, x i := by simp
      _ = ∏ j, x j := Finset.prod_congr rfl (fun j _ => (hconst j).1.symm)
      _ = 1 := c.productX_active (ne_of_gt hX)
  have hyp : y i ^ N = 1 := by
    by_cases hY : c.productY = 0
    · rw [c.one_product_other_eq_one hx hy hS hX hY i, one_pow]
    · calc
        _ = ∏ _j : Fin N, y i := by simp
        _ = ∏ j, y j := Finset.prod_congr rfl (fun j _ => (hconst j).2.symm)
        _ = 1 := c.productY_active hY
  obtain ⟨l,hl⟩ := root_eq_angleRoot (ne_of_gt hN) hxp
  obtain ⟨m,hm⟩ := root_eq_angleRoot (ne_of_gt hN) hyp
  refine ⟨hs₀,l,m,?_⟩
  have hd := c.dispersion_active i (ne_of_gt (c.lowerX_of_productX_pos hx hX i).1)
  simp only [hl,hm,PrimeFamily.angleRoot,Complex.exp_ofReal_mul_I_re] at hd
  rw [hrel]
  exact_mod_cast hd.symm

/-- All coefficients vanish at a non-Nickel point. Pair coefficients vanish
first; the dispersion-only case uses the strict level interval (0,2). -/
theorem ActiveCombination.zero_of_nonNickel {N : ℕ} (hN : 0 < N)
    {x y : Fin N → ℂ} {S : ℝ} {s₀ : ℂ}
    (c : ActiveCombination x y S)
    (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (hS : 0 < S ∧ S < 2) (hs₀ : ‖s₀‖ = 1) (hrel : s₀+s₀⁻¹ = (S:ℂ))
    (hn : ¬ PrimeFamily.NickelAt s₀ N) :
    c.productX = 0 ∧ c.productY = 0 ∧
      (∀ i j, c.pairX i j = 0) ∧ (∀ i j, c.pairY i j = 0) ∧
      (∀ i, c.dispersionWeight i = 0) := by
  have hX : c.productX = 0 := by
    by_contra h
    exact hn (c.nickel_of_productX_pos hN hx hy hS.1 hs₀ hrel
      (lt_of_le_of_ne c.productX_nonneg (Ne.symm h)))
  have hY : c.productY = 0 := by
    by_contra h
    exact hn (c.swap.nickel_of_productX_pos hN hy hx hS.1 hs₀ hrel
      (lt_of_le_of_ne c.productY_nonneg (Ne.symm h)))
  exact ⟨hX,hY,c.pairX_eq_zero hx,c.pairY_eq_zero hy,
    c.dispersion_eq_zero_of_products_zero hx hy hS hX hY⟩

/-- Finite-dimensional convex separation, proved for the actual source
vectors at each non-Nickel torus point. -/
theorem nonNickel_active_separated {N : ℕ} (hN : 0 < N)
    {x y : Fin N → ℂ} {S : ℝ} {s₀ : ℂ}
    (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (hS : 0 < S ∧ S < 2) (hs₀ : ‖s₀‖ = 1) (hrel : s₀+s₀⁻¹ = (S:ℂ))
    (hn : ¬ PrimeFamily.NickelAt s₀ N) : ActiveSourceSeparated x y S := by
  classical
  let P := singularFactorActive x y S
  let V := activeSingularVectorSet x y S
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
    have hc := c.zero_of_nonNickel hN hx hy hS hs₀ hrel hn
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
end IsingBulk.First
