import IsingBulk.First.ComplementSeparation

/-! The no-product-factor specialization required internally for the onsite
term in the full-site/offsite normalization bridge. -/
namespace IsingBulk.First
noncomputable section
open scoped BigOperators
open Set

/-- With the two global products absent, every nonnegative active zero
combination vanishes at every torus point on a positive level below two. -/
theorem active_vector_zero_without_products {N : ℕ} {x y : Fin N → ℂ} {S : ℝ}
    (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1) (hS : 0 < S ∧ S < 2)
    (w : SingularFactorIndex N → ℝ) (hw : ∀ f, 0 ≤ w f)
    (hact : ∀ f, w f ≠ 0 → singularFactorActive x y S f)
    (hX : w (.inl false) = 0) (hY : w (.inl true) = 0)
    (hsum : ∑ f, w f • singularFactorVector x y f = 0) : ∀ f, w f = 0 := by
  let c := activeCombinationOfVectorSum w hw hact hsum
  have hpx := c.pairX_eq_zero hx
  have hpy := c.pairY_eq_zero hy
  have hz := c.dispersion_eq_zero_of_products_zero hx hy hS hX hY
  rintro (b | (⟨b, i, j⟩ | i))
  · cases b
    · exact hX
    · exact hY
  · cases b
    · exact hpx i j
    · exact hpy i j
  · exact hz i

/-- The onsite coefficient has only pair and dispersion factors. -/
abbrev OnsiteFactorIndex (N : ℕ) := (Bool × Fin N × Fin N) ⊕ Fin N

def onsiteVectorSet {N : ℕ} (x y : Fin N → ℂ) (S : ℝ) :
    Set (DoubleAngularVector N) :=
  range (fun f : {f : OnsiteFactorIndex N // singularFactorActive x y S (.inr f)} =>
    singularFactorVector x y (.inr f.val))

/-- No excluded selected chart is needed for the actual onsite active set. -/
theorem zero_not_mem_onsite_convexHull {N : ℕ} {x y : Fin N → ℂ} {S : ℝ}
    (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1) (hS : 0 < S ∧ S < 2) :
    (0 : DoubleAngularVector N) ∉ convexHull ℝ (onsiteVectorSet x y S) := by
  classical
  let P : OnsiteFactorIndex N → Prop := fun f => singularFactorActive x y S (.inr f)
  change (0 : DoubleAngularVector N) ∉ convexHull ℝ
    (range (fun f : {f : OnsiteFactorIndex N // P f} => singularFactorVector x y (.inr f.val)))
  apply zero_not_mem_convexHull_range_of_nonnegative_relation
  intro w hw hsum
  let W : OnsiteFactorIndex N → ℝ := fun f => if hf : P f then w ⟨f, hf⟩ else 0
  let V : SingularFactorIndex N → ℝ := Sum.elim (fun _ => 0) W
  have hW : ∀ f, 0 ≤ W f := by
    intro f
    by_cases hf : P f
    · simpa [W, hf] using hw ⟨f, hf⟩
    · simp [W, hf]
  have hV : ∀ f, 0 ≤ V f := by
    rintro (b | f)
    · exact le_rfl
    · exact hW f
  have hact : ∀ f, V f ≠ 0 → singularFactorActive x y S f := by
    rintro (b | f) hf
    · exact False.elim (hf rfl)
    · by_contra hnf
      exact hf (by simp [V, W, P, hnf])
  have hv : ∑ f, V f • singularFactorVector x y f = 0 := by
    rw [Fintype.sum_sum_type]
    simp only [V, Sum.elim_inl, Sum.elim_inr, zero_smul,
      Finset.sum_const_zero, zero_add]
    rw [← Fintype.sum_subtype_add_sum_subtype P]
    have h₁ : (∑ f : {f : OnsiteFactorIndex N // P f},
        W f.val • singularFactorVector x y (.inr f.val)) =
        ∑ f, w f • singularFactorVector x y (.inr f.val) := by
      apply Finset.sum_congr rfl
      intro f _
      simp [W, f.property]
    have h₂ : (∑ f : {f : OnsiteFactorIndex N // ¬P f},
        W f.val • singularFactorVector x y (.inr f.val)) = 0 := by
      apply Finset.sum_eq_zero
      intro f _
      simp [W, f.property]
    rw [h₁, h₂, add_zero]
    exact hsum
  have hz := active_vector_zero_without_products hx hy hS V hV hact rfl rfl hv
  intro f
  simpa [V, W, f.property] using hz (.inr f.val)

/-- The onsite active vectors have a positive real separator everywhere on
the actual limiting torus at the selected positive level. -/
theorem onsite_separating_functional {N : ℕ} {x y : Fin N → ℂ} {S : ℝ}
    (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1) (hS : 0 < S ∧ S < 2) :
    ∃ (f : StrongDual ℝ (DoubleAngularVector N)) (δ : ℝ), 0 < δ ∧
      ∀ i : OnsiteFactorIndex N, singularFactorActive x y S (.inr i) →
        δ < f (singularFactorVector x y (.inr i)) := by
  classical
  let V := onsiteVectorSet x y S
  have hfin : V.Finite := Set.finite_range _
  obtain ⟨f, δ, hδ, hf⟩ := geometric_hahn_banach_point_closed (convex_convexHull ℝ V)
    (hfin.isCompact_convexHull ℝ).isClosed (zero_not_mem_onsite_convexHull hx hy hS)
  refine ⟨f, δ, by simpa using hδ, ?_⟩
  intro i hi
  exact hf _ (subset_convexHull ℝ V ⟨⟨i, hi⟩, rfl⟩)

end
end IsingBulk.First
