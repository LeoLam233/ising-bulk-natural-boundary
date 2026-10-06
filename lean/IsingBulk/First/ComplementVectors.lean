import IsingBulk.First.ComplementGeometry
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation

/-! Actual active singular-factor vectors and finite separation for FIRST. -/
namespace IsingBulk.First
noncomputable section
open scoped BigOperators
open Set

/-- False labels the x block and true labels the y block. -/
abbrev SingularFactorIndex (N : ℕ) := Bool ⊕ ((Bool × Fin N × Fin N) ⊕ Fin N)
abbrev DoubleAngularVector (N : ℕ) := (Fin N → ℝ) × (Fin N → ℝ)

/-- The exact vectors appearing as limiting imaginary exponent gradients. -/
def singularFactorVector {N : ℕ} (x y : Fin N → ℂ) :
    SingularFactorIndex N → DoubleAngularVector N
  | .inl false => (fun _ => 1, fun _ => 0)
  | .inl true => (fun _ => 0, fun _ => 1)
  | .inr (.inl (false, i, j)) => (Pi.single i 1 + Pi.single j 1, 0)
  | .inr (.inl (true, i, j)) => (0, Pi.single i 1 + Pi.single j 1)
  | .inr (.inr i) => (Pi.single i (x i).im, Pi.single i (y i).im)

/-- Activation refers to the actual product, pair, and dispersion denominators. -/
def singularFactorActive {N : ℕ} (x y : Fin N → ℂ) (S : ℝ) :
    SingularFactorIndex N → Prop
  | .inl false => ∏ i, x i = 1
  | .inl true => ∏ i, y i = 1
  | .inr (.inl (false, i, j)) => i < j ∧ x i * x j = 1
  | .inr (.inl (true, i, j)) => i < j ∧ y i * y j = 1
  | .inr (.inr i) => (x i).re + (y i).re = S

/-- Projection of the finite vector combination onto an x coordinate. -/
theorem singularFactorVector_sum_x {N : ℕ} (x y : Fin N → ℂ)
    (w : SingularFactorIndex N → ℝ) (i : Fin N) :
    (∑ f, w f • singularFactorVector x y f).1 i =
      w (.inl false) +
      (∑ j, (w (.inr (.inl (false, i, j))) + w (.inr (.inl (false, j, i))))) +
      w (.inr (.inr i)) * (x i).im := by
  classical
  simp [Fintype.sum_sum_type, Fintype.sum_prod_type, singularFactorVector,
    Finset.sum_add_distrib, Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
  ring

/-- Projection of the finite vector combination onto a y coordinate. -/
theorem singularFactorVector_sum_y {N : ℕ} (x y : Fin N → ℂ)
    (w : SingularFactorIndex N → ℝ) (i : Fin N) :
    (∑ f, w f • singularFactorVector x y f).2 i =
      w (.inl true) +
      (∑ j, (w (.inr (.inl (true, i, j))) + w (.inr (.inl (true, j, i))))) +
      w (.inr (.inr i)) * (y i).im := by
  classical
  simp [Fintype.sum_sum_type, Fintype.sum_prod_type, singularFactorVector,
    Finset.sum_add_distrib, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  ring

/-- Convert a genuine vector equality to the coordinate coefficient interface.
This constructor proves the balance fields; they are not extra source premises. -/
def activeCombinationOfVectorSum {N : ℕ} {x y : Fin N → ℂ} {S : ℝ}
    (w : SingularFactorIndex N → ℝ) (hw : ∀ f, 0 ≤ w f)
    (hact : ∀ f, w f ≠ 0 → singularFactorActive x y S f)
    (hsum : ∑ f, w f • singularFactorVector x y f = 0) : ActiveCombination x y S where
  productX := w (.inl false)
  productY := w (.inl true)
  pairX := fun i j => w (.inr (.inl (false, i, j)))
  pairY := fun i j => w (.inr (.inl (true, i, j)))
  dispersionWeight := fun i => w (.inr (.inr i))
  productX_nonneg := hw _
  productY_nonneg := hw _
  pairX_nonneg := fun i j => hw _
  pairY_nonneg := fun i j => hw _
  dispersion_nonneg := fun i => hw _
  productX_active := hact _
  productY_active := hact _
  pairX_active := fun i j => hact _
  pairY_active := fun i j => hact _
  dispersion_active := fun i => hact _
  balanceX := fun i => by
    have h := congrArg (fun v : DoubleAngularVector N => v.1 i) hsum
    simpa only [singularFactorVector_sum_x, Prod.fst_zero, Pi.zero_apply] using h
  balanceY := fun i => by
    have h := congrArg (fun v : DoubleAngularVector N => v.2 i) hsum
    simpa only [singularFactorVector_sum_y, Prod.snd_zero, Pi.zero_apply] using h

/-- Every coefficient of a genuine nonnegative active vector zero sum is zero
away from the two selected configurations. -/
theorem active_vector_zero_coefficients {p : ℕ} {a b : ℤ}
    {x y : Fin (2*p) → ℂ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (ha : PrimeFamily.Admissible p a) (hb : PrimeFamily.Admissible p b)
    (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (hgood : ¬ selectedBadConfiguration a b x y)
    (w : SingularFactorIndex (2*p) → ℝ) (hw : ∀ f, 0 ≤ w f)
    (hact : ∀ f, w f ≠ 0 → singularFactorActive x y (2 * PrimeFamily.cosineAverage p a b) f)
    (hsum : ∑ f, w f • singularFactorVector x y f = 0) : ∀ f, w f = 0 := by
  let c := activeCombinationOfVectorSum w hw hact hsum
  have h := c.zero_off_selected hp hp11 ha hb hx hy hgood
  rintro (b | (⟨b, i, j⟩ | i))
  · cases b
    · exact h.1
    · exact h.2.1
  · cases b
    · exact h.2.2.1 i j
    · exact h.2.2.2.1 i j
  · exact h.2.2.2.2 i

/-- A finite family without a nontrivial nonnegative relation has convex hull
separated from zero. The normalization of convex weights is used explicitly. -/
theorem zero_not_mem_convexHull_range_of_nonnegative_relation
    {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E]
    (v : ι → E)
    (h : ∀ w : ι → ℝ, (∀ i, 0 ≤ w i) → (∑ i, w i • v i = 0) → ∀ i, w i = 0) :
    (0 : E) ∉ convexHull ℝ (range v) := by
  classical
  rw [convexHull_range_eq_exists_affineCombination]
  rintro ⟨s, w, hw, hsum, hv⟩
  let w' : ι → ℝ := fun i => if i ∈ s then w i else 0
  have hw' : ∀ i, 0 ≤ w' i := by
    intro i
    by_cases hi : i ∈ s
    · simpa [w', hi] using hw i hi
    · simp [w', hi]
  have hsum' : ∑ i, w' i = 1 := by
    simpa only [w', Fintype.sum_ite_mem] using hsum
  have hv' : ∑ i, w' i • v i = 0 := by
    rw [Finset.affineCombination_eq_linear_combination s v w hsum] at hv
    simpa only [w', ite_smul, zero_smul, Fintype.sum_ite_mem] using hv
  have hz := h w' hw' hv'
  simp [hz] at hsum'

/-- The active subtype keeps inactive factors out of the convex hull. -/
def activeSingularVectorSet {N : ℕ} (x y : Fin N → ℂ) (S : ℝ) :
    Set (DoubleAngularVector N) :=
  range (fun f : {f : SingularFactorIndex N // singularFactorActive x y S f} =>
    singularFactorVector x y f.val)

/-- Actual active vectors have no zero convex combination off the two charts. -/
theorem zero_not_mem_active_convexHull {p : ℕ} {a b : ℤ}
    {x y : Fin (2*p) → ℂ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (ha : PrimeFamily.Admissible p a) (hb : PrimeFamily.Admissible p b)
    (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (hgood : ¬ selectedBadConfiguration a b x y) :
    (0 : DoubleAngularVector (2*p)) ∉
      convexHull ℝ (activeSingularVectorSet x y (2 * PrimeFamily.cosineAverage p a b)) := by
  classical
  let P := singularFactorActive x y (2 * PrimeFamily.cosineAverage p a b)
  change (0 : DoubleAngularVector (2*p)) ∉
    convexHull ℝ (range (fun f : {f : SingularFactorIndex (2*p) // P f} =>
      singularFactorVector x y f.val))
  apply zero_not_mem_convexHull_range_of_nonnegative_relation
  intro w hw hsum
  let W : SingularFactorIndex (2*p) → ℝ := fun f => if hf : P f then w ⟨f, hf⟩ else 0
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
    have h₁ : (∑ f : {f : SingularFactorIndex (2*p) // P f},
        W f.val • singularFactorVector x y f.val) =
        ∑ f, w f • singularFactorVector x y f.val := by
      apply Finset.sum_congr rfl
      intro f _
      simp [W, f.property]
    have h₂ : (∑ f : {f : SingularFactorIndex (2*p) // ¬P f},
        W f.val • singularFactorVector x y f.val) = 0 := by
      apply Finset.sum_eq_zero
      intro f _
      simp [W, f.property]
    rw [h₁, h₂, add_zero]
    exact hsum
  have hz := active_vector_zero_coefficients hp hp11 ha hb hx hy hgood W hW hact hv
  intro f
  simpa [W, f.property] using hz f.val

/-- A positive separating functional for every active source vector, obtained
from the proved classification rather than inserted as a setup hypothesis. -/
theorem selected_active_separating_functional {p : ℕ} {a b : ℤ}
    {x y : Fin (2*p) → ℂ} (hp : p.Prime) (hp11 : 11 ≤ p)
    (ha : PrimeFamily.Admissible p a) (hb : PrimeFamily.Admissible p b)
    (hx : ∀ i, ‖x i‖ = 1) (hy : ∀ i, ‖y i‖ = 1)
    (hgood : ¬ selectedBadConfiguration a b x y) :
    ∃ (f : StrongDual ℝ (DoubleAngularVector (2*p))) (δ : ℝ),
      0 < δ ∧ ∀ i, singularFactorActive x y (2 * PrimeFamily.cosineAverage p a b) i →
        δ < f (singularFactorVector x y i) := by
  classical
  let V := activeSingularVectorSet x y (2 * PrimeFamily.cosineAverage p a b)
  have hfin : V.Finite := Set.finite_range _
  have hsep := geometric_hahn_banach_point_closed (convex_convexHull ℝ V)
    (hfin.isCompact_convexHull ℝ).isClosed
    (zero_not_mem_active_convexHull hp hp11 ha hb hx hy hgood)
  obtain ⟨f, δ, hδ, hf⟩ := hsep
  refine ⟨f, δ, by simpa using hδ, ?_⟩
  intro i hi
  exact hf _ (subset_convexHull ℝ V ⟨⟨i, hi⟩, rfl⟩)

end
end IsingBulk.First
