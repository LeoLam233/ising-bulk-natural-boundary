import Mathlib.Analysis.Calculus.FDeriv.ContinuousAlternatingMap
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-!
# Jacobi differentiation for the scalar complex current

The determinant is differentiated as a continuous alternating map.
The trace formula is derived from the row replacement identity. These
are generic checked identities for the actual scalar Jacobian, without
assuming a change of measure to a complex constrained hyperplane.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def scalarDeterminant : (ι → ℂ) [⋀^ι]→L[ℂ] ℂ :=
  { (Matrix.detRowAlternating : (ι → ℂ) [⋀^ι]→ₗ[ℂ] ℂ) with
    cont := continuous_id.matrix_det }

@[simp] theorem scalarDeterminant_apply (M : Matrix ι ι ℂ) :
    scalarDeterminant M = M.det := rfl

def scalarDeterminantDerivative (M H : Matrix ι ι ℂ) : ℂ :=
  ∑ i, (M.updateRow i (H i)).det

def scalarJacobiTrace (M H : Matrix ι ι ℂ) : ℂ := (H * M⁻¹).trace * M.det

theorem scalarDeterminantDerivative_mul (M A : Matrix ι ι ℂ) :
    scalarDeterminantDerivative M (A * M) = A.trace * M.det := by
  unfold scalarDeterminantDerivative Matrix.trace
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  have hrow : (A * M) i = ∑ j, A i j • M j := by
    ext k
    simp only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hrow, Matrix.det_updateRow_sum, smul_eq_mul]
  rfl

theorem scalarDeterminantDerivative_trace (M H : Matrix ι ι ℂ) (hM : M.det ≠ 0) :
    scalarDeterminantDerivative M H = (H * M⁻¹).trace * M.det := by
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  have he : (H * M⁻¹) * M = H := by rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul M hunit, Matrix.mul_one]
  calc
    scalarDeterminantDerivative M H = scalarDeterminantDerivative M ((H * M⁻¹) * M) := by rw [he]
    _ = (H * M⁻¹).trace * M.det := scalarDeterminantDerivative_mul M (H * M⁻¹)

theorem scalarDeterminant_hasFDerivAt (M : ι → ι → ℂ) :
    HasFDerivAt (fun A : ι → ι → ℂ => Matrix.det A)
      ((scalarDeterminant (ι := ι)).toContinuousMultilinearMap.linearDeriv M) M := by
  exact (scalarDeterminant (ι := ι)).hasFDerivAt M

theorem scalarDeterminant_fderiv_apply (M H : ι → ι → ℂ) :
    fderiv ℂ (fun A : ι → ι → ℂ => Matrix.det A) M H = scalarDeterminantDerivative M H := by
  rw [(scalarDeterminant_hasFDerivAt M).fderiv, ContinuousMultilinearMap.linearDeriv_apply]
  rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The real directional derivative of the actual complex determinant.
This is the derivative needed for real angular integration by parts. -/
theorem scalarDeterminant_real_fderiv_apply (M : E → ι → ι → ℂ)
    (x h : E) (hM : DifferentiableAt ℝ M x) :
    fderiv ℝ (fun y => Matrix.det (M y)) x h =
      scalarDeterminantDerivative (M x) (fderiv ℝ M x h) := by
  have hd := ((scalarDeterminant (ι := ι)).restrictScalars ℝ).hasFDerivAt (M x)
  have hc := hd.comp x hM.hasFDerivAt
  change fderiv ℝ ((scalarDeterminant (ι := ι)).restrictScalars ℝ ∘ M) x h = _
  rw [hc.fderiv, ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.linearDeriv_apply]
  rfl

/-- Jacobi's formula on a real parameter/angle space, with the complete
complex matrix and its genuine real derivative. -/
theorem scalarJacobi_real (M : E → ι → ι → ℂ) (x h : E)
    (hM : DifferentiableAt ℝ M x) (hdet : Matrix.det (M x) ≠ 0) :
    fderiv ℝ (fun y => Matrix.det (M y)) x h =
      scalarJacobiTrace (M x) (fderiv ℝ M x h) := by
  rw [scalarDeterminant_real_fderiv_apply M x h hM]
  exact scalarDeterminantDerivative_trace (M x) (fderiv ℝ M x h) hdet

end IsingBulk.AnisoF002.Isotropic
