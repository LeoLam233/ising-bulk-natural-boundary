import IsingBulk.Tail.SelectorSourcePiola
import IsingBulk.First.SymmetryAlgebra

/-!
# The HT signed reduced kernel

The two signs in HT-1.0, Section 5, change only the two global product
kernels.  The actual canceled pairs, residue factors, occupancy-dependent
contour and Jacobian are the LT definitions.  No particle parity is assumed
in this file, and no tail estimate or contour identity is a hypothesis.
-/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Tail
open scoped BigOperators

/-- The literal signed global rational factor from HT-1.0 Section 5. -/
def signedGlobalFactor (σ Z Y : ℂ) : ℂ :=
  (Z⁻¹ + Y⁻¹) / ((1 - σ * Z) * (1 - σ * Y))

/-- The actual reduced density.  All local factors are reused unchanged. -/
def signedCanceledDensity {N : ℕ} (σ : ℂ) (z y : Fin N → ℂ) : ℂ :=
  signedGlobalFactor σ (coordinateProduct z) (coordinateProduct y) *
    canceledPairProduct z y * ∏ i, residueFactor (z i)

@[simp] theorem signedCanceledDensity_one {N : ℕ} (z y : Fin N → ℂ) :
    signedCanceledDensity 1 z y = canceledReducedDensity z y := by
  simp [signedCanceledDensity, signedGlobalFactor, canceledReducedDensity]

/-- The unit-circle kernel gap is independent of the sign. -/
theorem signed_gap_lower (σ z : ℂ) (hσ : ‖σ‖ = 1) :
    1 - ‖z‖ ≤ ‖1 - σ * z‖ := by
  simpa only [norm_one, norm_mul, hσ, one_mul] using
    norm_sub_norm_le (1 : ℂ) (σ * z)

theorem signed_gap_ne_zero (σ z : ℂ) (hσ : ‖σ‖ = 1) (hz : ‖z‖ < 1) :
    1 - σ * z ≠ 0 := by
  intro he
  have h := signed_gap_lower σ z hσ
  rw [he, norm_zero] at h
  linarith

theorem signed_product_gap_ne_zero {N : ℕ} (hN : 0 < N) (σ : ℂ)
    (hσ : ‖σ‖ = 1) (z : Fin N → ℂ) (hz : ∀ i, ‖z i‖ < 1) :
    1 - σ * coordinateProduct z ≠ 0 :=
  signed_gap_ne_zero σ _ hσ (coordinateProduct_norm_lt_one hN hz)

/-- Comparing with the established unsigned density is an exact identity;
no estimate is inferred by dividing by a pair or a Vandermonde zero. -/
theorem signedCanceledDensity_eq_correction {N : ℕ} (σ : ℂ)
    (z y : Fin N → ℂ)
    (hZ : 1 - coordinateProduct z ≠ 0)
    (hY : 1 - coordinateProduct y ≠ 0) :
    signedCanceledDensity σ z y = canceledReducedDensity z y *
      (((1 - coordinateProduct z) * (1 - coordinateProduct y)) /
        ((1 - σ * coordinateProduct z) * (1 - σ * coordinateProduct y))) := by
  let A := (1-coordinateProduct z)*(1-coordinateProduct y)
  let B := (1-σ*coordinateProduct z)*(1-σ*coordinateProduct y)
  let Q := (coordinateProduct z)⁻¹+(coordinateProduct y)⁻¹
  let P := canceledPairProduct z y
  let R := ∏ i,residueFactor (z i)
  have hA : A ≠ 0 := mul_ne_zero hZ hY
  change Q/B*P*R = (Q/A*P*R)*(A/B)
  simp only [div_eq_mul_inv]
  calc
    _ = (Q*P*R*B⁻¹)*(A⁻¹*A) := by rw [inv_mul_cancel₀ hA]; ring
    _ = _ := by ring


/-- Signed kernel domination uses the actual product moduli, so it remains
valid on a protected disk where individual compact roots may leave the disk. -/
theorem signedGlobalFactor_norm_le {σ Z Y : ℂ} (hσ : ‖σ‖ = 1)
    {A gZ gY : ℝ} (hA : ‖Z⁻¹‖ + ‖Y⁻¹‖ ≤ A)
    (hgZ : 0 < gZ) (hgY : 0 < gY)
    (hZ : ‖Z‖ ≤ 1 - gZ) (hY : ‖Y‖ ≤ 1 - gY) :
    ‖signedGlobalFactor σ Z Y‖ ≤ A / (gZ * gY) := by
  have hZG : gZ ≤ ‖1 - σ * Z‖ := by
    have h := signed_gap_lower σ Z hσ
    linarith
  have hYG : gY ≤ ‖1 - σ * Y‖ := by
    have h := signed_gap_lower σ Y hσ
    linarith
  have hnum : ‖Z⁻¹ + Y⁻¹‖ ≤ A := (norm_add_le _ _).trans hA
  have hden : gZ * gY ≤ ‖1 - σ * Z‖ * ‖1 - σ * Y‖ :=
    mul_le_mul hZG hYG hgY.le (norm_nonneg _)
  rw [signedGlobalFactor, norm_div, norm_mul]
  exact div_le_div₀ ((norm_nonneg _).trans hnum) hnum (mul_pos hgZ hgY) hden

/-- Every root and both signed product kernels are legal on the complete
real homotopy.  The radius is an independent fixed parameter. -/
theorem signed_homotopy_legal {N : ℕ} (hN : 0 < N)
    (σ : ℂ) (hσ : ‖σ‖ = 1) (f : SelectorFunctions)
    {r τ lam : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hτ : 0 ≤ τ) (hlam : 0 ≤ lam) (s : ℂ)
    (hmargin : r⁻¹ - r < (sourceS s).im)
    (hp : ∀ x, 0 ≤ f.p x) (hm0 : ∀ x, 0 ≤ f.m x)
    (hm1 : ∀ x, f.m x ≤ 1)
    (hps : ∀ x, Real.sin x ≤ 0 → f.p x = 0)
    (hms : ∀ x, 0 ≤ Real.sin x → f.m x = 0) (θ : Fin N → ℝ) :
    (∀ i, ‖globalRoot s (deformedPoint f r τ lam θ i)‖ < 1 ∧
      (globalRoot s (deformedPoint f r τ lam θ i)).im < 0) ∧
    1 - σ * coordinateProduct (deformedPoint f r τ lam θ) ≠ 0 ∧
    1 - σ * coordinateProduct
      (fun i => globalRoot s (deformedPoint f r τ lam θ i)) ≠ 0 := by
  have hz := homotopy_root_interior hN f hr hr1 hτ hlam θ s hmargin hp hm0 hps hms
  exact ⟨hz,
    signed_gap_ne_zero σ _ hσ
      (homotopy_y_product_lt_one hN f hr hr1 hτ hlam θ hp hm1),
    signed_product_gap_ne_zero hN σ hσ _ (fun i => (hz i).1)⟩

end
end IsingBulk.HT.Contour
