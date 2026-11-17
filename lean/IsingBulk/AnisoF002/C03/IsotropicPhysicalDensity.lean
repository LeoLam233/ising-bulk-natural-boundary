import IsingBulk.AnisoF002.C03.IsotropicActualCoordinates
import IsingBulk.AnisoF002.C03.IsotropicOneSidedRetainedJets

/-!
# The physical scalar density in the actual regular coordinates

The determinant is the derivative of the actual regular-coordinate map
with respect to the original real angles. Its factorization is proved
from that derivative. The one-body cancellation is an exact scalar
identity on the upper physical sheet, with no new complex measure.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators Matrix
open Set Metric
open IsingBulk.AnisoF002.RegularTail

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def actualAngularDirection (i : ι) : ℂ × (ι → ℝ) := (0, Pi.single i 1)

def actualBalancedMatrix (η τ ξ : ℝ) (θ : ι → ℝ) : Matrix ι ι ℂ :=
  LinearMap.toMatrix' (actualBalancedJacobian η τ ξ θ)

def actualPhysicalPhase (η τ ξ : ℝ) (q : ℂ × (ι → ℝ)) (i : ι) : ℂ :=
  upperPhysicalPhase (isotropicDispersion (q.1, actualHomotopyAngle η τ ξ q.2 i))

def actualCoordinateMultiplier (η τ ξ : ℝ) (q : ℂ × (ι → ℝ)) (i : ι) : ℂ :=
  1 - Complex.sin (actualHomotopyAngle η τ ξ q.2 i) / Complex.sin (actualPhysicalPhase η τ ξ q i)

def actualCoordinateDeterminant (η τ ξ : ℝ) (q : ℂ × (ι → ℝ)) : ℂ :=
  scalarCoordinateDet (actualPhysicalCoordinate η τ ξ) actualAngularDirection q

theorem actualPhysicalCoordinate_matrix (η τ ξ : ℝ) (q : ℂ × (ι → ℝ))
    (hq : ∀ i, 0 < (isotropicDispersion (q.1, actualHomotopyAngle η τ ξ q.2 i)).im) :
    scalarCoordinateMatrix (actualPhysicalCoordinate η τ ξ) actualAngularDirection q =
      Matrix.diagonal (actualCoordinateMultiplier η τ ξ q) * actualBalancedMatrix η τ ξ q.2 := by
  apply Matrix.ext
  intro i j
  change fderiv ℝ (actualPhysicalCoordinate η τ ξ i) q (actualAngularDirection j) = _
  rw [actualPhysicalCoordinate_fderiv η τ ξ i q (actualAngularDirection j) (hq i),
    Matrix.diagonal_mul]
  have he : (fun k => (((Pi.single j (1 : ℝ) : ι → ℝ) k) : ℂ)) =
      (Pi.single j (1 : ℂ) : ι → ℂ) := by
    funext k
    by_cases h : j = k
    · subst k
      simp
    · simp [h]
  simp only [actualAngularDirection, zero_div, sub_zero, he,
    actualCoordinateMultiplier, actualPhysicalPhase, actualBalancedMatrix, LinearMap.toMatrix'_apply]

theorem actualCoordinateDeterminant_factorization (η τ ξ : ℝ) (q : ℂ × (ι → ℝ))
    (hq : ∀ i, 0 < (isotropicDispersion (q.1, actualHomotopyAngle η τ ξ q.2 i)).im) :
    actualCoordinateDeterminant η τ ξ q =
      (actualBalancedJacobian η τ ξ q.2).det * ∏ i, actualCoordinateMultiplier η τ ξ q i := by
  unfold actualCoordinateDeterminant scalarCoordinateDet
  rw [actualPhysicalCoordinate_matrix η τ ξ q hq, Matrix.det_mul, Matrix.det_diagonal]
  rw [actualBalancedMatrix, LinearMap.det_toMatrix']
  exact mul_comm _ _

theorem coordinateMultiplier_ne_zero (w φ : ℂ) (hφ : Complex.sin φ ≠ 0)
    (hD : Complex.sin φ - Complex.sin w ≠ 0) :
    1 - Complex.sin w / Complex.sin φ ≠ 0 := by
  have he : 1 - Complex.sin w / Complex.sin φ =
      (Complex.sin φ - Complex.sin w) / Complex.sin φ := by field_simp
  rw [he]
  exact div_ne_zero hD hφ

theorem coordinateMultiplier_oneBody (w φ : ℂ) (hφ : Complex.sin φ ≠ 0)
    (hD : Complex.sin φ - Complex.sin w ≠ 0) :
    (1 - Complex.sin w / Complex.sin φ) * regularOneBody w φ =
      (Complex.sinh (Complex.I * φ))⁻¹ := by
  rw [← regularOneBody_eq_quotient w φ hφ hD]
  field_simp

theorem actualCoordinateDeterminant_ne_zero (η τ ξ : ℝ) (q : ℂ × (ι → ℝ))
    (hq : ∀ i, 0 < (isotropicDispersion (q.1, actualHomotopyAngle η τ ξ q.2 i)).im)
    (hM : Function.Injective (actualBalancedJacobian η τ ξ q.2))
    (hD : ∀ i, Complex.sin (actualPhysicalPhase η τ ξ q i) -
      Complex.sin (actualHomotopyAngle η τ ξ q.2 i) ≠ 0) :
    actualCoordinateDeterminant η τ ξ q ≠ 0 := by
  rw [actualCoordinateDeterminant_factorization η τ ξ q hq]
  apply mul_ne_zero
  · intro hz
    exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hz) (LinearMap.ker_eq_bot.mpr hM)
  · apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact coordinateMultiplier_ne_zero _ _ (upperPhysicalPhase_sin_ne_zero _ (hq i)) (hD i)

theorem actual_regular_scalar_density (η τ ξ : ℝ) (q : ℂ × (ι → ℝ))
    (hq : ∀ i, 0 < (isotropicDispersion (q.1, actualHomotopyAngle η τ ξ q.2 i)).im)
    (hU : ∀ i, explicitRightInverse (q.1, actualPhysicalCoordinate η τ ξ i q) =
      actualHomotopyAngle η τ ξ q.2 i)
    (hD : ∀ i, Complex.sin (actualPhysicalPhase η τ ξ q i) -
      Complex.sin (actualHomotopyAngle η τ ξ q.2 i) ≠ 0) :
    actualCoordinateDeterminant η τ ξ q *
        (∏ i, regularInverseOneBody (q.1, actualPhysicalCoordinate η τ ξ i q)) =
      (actualBalancedJacobian η τ ξ q.2).det *
        ∏ i, (Complex.sinh (Complex.I * actualPhysicalPhase η τ ξ q i))⁻¹ := by
  rw [actualCoordinateDeterminant_factorization η τ ξ q hq, mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [regularInverseOneBody, hU i]
  have he : actualPhysicalCoordinate η τ ξ i q - actualHomotopyAngle η τ ξ q.2 i =
      actualPhysicalPhase η τ ξ q i := by
    simp [actualPhysicalCoordinate, physicalRegularCoordinate, actualPhysicalPhase]
  rw [he]
  exact coordinateMultiplier_oneBody _ _ (upperPhysicalPhase_sin_ne_zero _ (hq i)) (hD i)

/-- The entire pair product is the original canceled physical product,
and the Jacobian-one-body identity holds simultaneously with it. -/
theorem actual_complete_scalar_density {N : ℕ} (η τ ξ : ℝ) (q : ℂ × (Fin N → ℝ))
    (hq : ∀ i, 0 < (isotropicDispersion (q.1, actualHomotopyAngle η τ ξ q.2 i)).im)
    (hU : ∀ i, explicitRightInverse (q.1, actualPhysicalCoordinate η τ ξ i q) =
      actualHomotopyAngle η τ ξ q.2 i)
    (hD : ∀ i, Complex.sin (actualPhysicalPhase η τ ξ q i) -
      Complex.sin (actualHomotopyAngle η τ ξ q.2 i) ≠ 0) :
    actualCoordinateDeterminant η τ ξ q *
        completeRegularNumerator N (q.1, fun i => actualPhysicalCoordinate η τ ξ i q) =
      (actualBalancedJacobian η τ ξ q.2).det *
        (∏ i, (Complex.sinh (Complex.I * actualPhysicalPhase η τ ξ q i))⁻¹) *
        ∏ ij ∈ indexPairs N,
          canceledPair 1
            (isotropicInteriorRoot (q.1, actualHomotopyAngle η τ ξ q.2 ij.1))
            (isotropicInteriorRoot (q.1, actualHomotopyAngle η τ ξ q.2 ij.2))
            (Complex.exp (actualHomotopyAngle η τ ξ q.2 ij.1 * Complex.I))
            (Complex.exp (actualHomotopyAngle η τ ξ q.2 ij.2 * Complex.I)) := by
  unfold completeRegularNumerator
  rw [← mul_assoc, actual_regular_scalar_density η τ ξ q hq hU hD]
  congr 1
  unfold completeInversePairProduct
  apply Finset.prod_congr rfl
  intro ij _
  exact inversePairFilled_physical_identification q.1 _ _ (hq ij.1) (hq ij.2) (hU ij.1) (hU ij.2)

/-- One actual whole one-sided neighborhood discharges every coordinate
regularity and density hypothesis. The size is selected before N and
includes both endpoint slivers and all homotopy times. -/
theorem exists_actual_oneSided_scalar_density (S η : ℝ)
    (hS : 0 < S ∧ S < 2) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (N : ℕ), 0 < N → ∀ (s : ℂ), 0 < s.im → dist s (S : ℂ) < δ →
      ∀ τ ∈ Icc 0 δ, ∀ ξ ∈ Icc 0 1, ∀ θ : Fin N → ℝ,
        (∀ i, θ i ∈ Icc (-Real.pi - δ) δ) →
        (∀ i, ContDiffAt ℝ 2 (actualPhysicalCoordinate η τ ξ i) (s, θ)) ∧
        actualCoordinateDeterminant η τ ξ (s, θ) ≠ 0 ∧
        actualCoordinateDeterminant η τ ξ (s, θ) *
            (∏ i, regularInverseOneBody (s, actualPhysicalCoordinate η τ ξ i (s, θ))) =
          (actualBalancedJacobian η τ ξ θ).det *
            ∏ i, (Complex.sinh (Complex.I * actualPhysicalPhase η τ ξ (s, θ) i))⁻¹ := by
  obtain ⟨r, hr, _, hdata, _⟩ := exists_oneSided_inverse_protected_neighborhood S hS
  obtain ⟨δ₁, hδ₁, himage⟩ := exists_actual_oneSided_homotopy_domain S r hS hr
  obtain ⟨δ₂, _, hδ₂, _, hregular⟩ := exists_actual_balanced_uniform_regularity η
  let δ := min δ₁ δ₂
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  have hd1 : δ ≤ δ₁ := min_le_left _ _
  have hd2 : δ ≤ δ₂ := min_le_right _ _
  refine ⟨δ, hδ, ?_⟩
  intro N hN s hs hsnear τ hτ ξ hξ θ hθ
  have ht1 : τ ∈ Icc 0 δ₁ := ⟨hτ.1, hτ.2.trans hd1⟩
  have ht2 : τ ∈ Icc 0 δ₂ := ⟨hτ.1, hτ.2.trans hd2⟩
  have hθ1 : ∀ i, θ i ∈ Icc (-Real.pi - δ₁) δ₁ :=
    fun i => ⟨by linarith [(hθ i).1], (hθ i).2.trans hd1⟩
  obtain ⟨hq, hU⟩ := himage N hN s hs (hsnear.trans_le hd1) η τ ξ hη ht1 hξ θ hθ1
  have hsheet (i : Fin N) : 0 < (isotropicDispersion (s, actualHomotopyAngle η τ ξ θ i)).im :=
    actual_balanced_homotopy_sheet s hs η τ ξ hη hτ.1 hξ.1 θ i
  have hD (i : Fin N) : Complex.sin (actualPhysicalPhase η τ ξ (s, θ) i) -
      Complex.sin (actualHomotopyAngle η τ ξ θ i) ≠ 0 := by
    have hd := (hdata (s, (actualHomotopyRegularTuple s η τ ξ θ).2 i)
      (thickening_subset_cthickening r _ (oneSidedSingle_of_thickening hq.1 (hq.2 i)))).2.2
    unfold explicitRightDenominator at hd
    rw [hU i] at hd
    simpa [actualHomotopyRegularTuple, physicalRegularCoordinate, actualPhysicalPhase] using hd
  have hbij := (hregular N hN τ ht2 ξ hξ θ).1
  exact ⟨fun i => actualPhysicalCoordinate_contDiffAt η τ ξ i (s, θ) 2 (hsheet i),
    actualCoordinateDeterminant_ne_zero η τ ξ (s, θ) hsheet hbij.1 hD,
    actual_regular_scalar_density η τ ξ (s, θ) hsheet hU hD⟩

end IsingBulk.AnisoF002.Isotropic
