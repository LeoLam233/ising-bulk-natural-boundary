import IsingBulk.AnisoF002.C03.IsotropicConstructedCurrent
import IsingBulk.AnisoF002.C03.IsotropicPeriodicCurrentIntegral

/-!
# The exact current for a holomorphic density pulled back by real coordinates

The angular velocity is constructed from the full coordinate derivative.
Complex linearity of the density derivative proves that its regular
time derivative vanishes. The resulting current is therefore an exact
divergence on the original real variables.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators Matrix
open Set Filter

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [DecidableEq ι] in
theorem scalarPartial_holomorphic_comp (χ : ι → E → ℂ) (F : (ι → ℂ) → ℂ) (x v : E)
    (hχ : ∀ i, DifferentiableAt ℝ (χ i) x)
    (hF : DifferentiableAt ℂ F (fun i => χ i x)) :
    scalarPartial (fun y => F (fun i => χ i y)) v x =
      fderiv ℂ F (fun i => χ i x) (fun i => scalarPartial (χ i) v x) := by
  have hm : DifferentiableAt ℝ (fun y => fun i => χ i y) x := differentiableAt_pi.mpr hχ
  have hd := (hF.hasFDerivAt.restrictScalars ℝ).comp x hm.hasFDerivAt
  simp only [Function.comp_def] at hd
  rw [scalarPartial, hd.fderiv, ContinuousLinearMap.comp_apply]
  have he : fderiv ℝ (fun y => fun i => χ i y) x v = fun i => scalarPartial (χ i) v x := by
    funext i
    rw [scalarPartial, fderiv_apply hm i, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  exact congrArg (fun w => fderiv ℂ F (fun i => χ i x) w) he

omit [DecidableEq ι] in
theorem complex_linear_matrix_column_sum (L : (ι → ℂ) →L[ℂ] ℂ)
    (M : Matrix ι ι ℂ) (v : ι → ℂ) :
    (∑ j, v j * L (fun i => M i j)) = L (M *ᵥ v) := by
  have he : M *ᵥ v = ∑ j, v j • (fun i => M i j) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  rw [he, map_sum]
  simp only [map_smul, smul_eq_mul]

theorem holomorphic_pullback_parameter_derivative_zero (χ : ι → E → ℂ) (e : ι → E)
    (a x : E) (F : (ι → ℂ) → ℂ)
    (hχ : ∀ i, DifferentiableAt ℝ (χ i) x)
    (hF : DifferentiableAt ℂ F (fun i => χ i x))
    (hdet : scalarCoordinateDet χ e x ≠ 0) :
    scalarRegularParameterDerivative χ e a (fun y => F (fun i => χ i y)) x = 0 := by
  let M : Matrix ι ι ℂ := scalarCoordinateMatrix χ e x
  let u := fun i => scalarPartial (χ i) a x
  let L := fderiv ℂ F (fun i => χ i x)
  have hMu : M *ᵥ (M⁻¹ *ᵥ u) = u := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]
  change scalarPartial (fun y => F (fun i => χ i y)) a x -
    (M⁻¹ *ᵥ u) ⬝ᵥ (fun i => scalarPartial (fun y => F (fun j => χ j y)) (e i) x) = 0
  rw [scalarPartial_holomorphic_comp χ F x a hχ hF]
  simp_rw [scalarPartial_holomorphic_comp χ F x _ hχ hF]
  change L u - (∑ j, (M⁻¹ *ᵥ u) j * L (fun i => M i j)) = 0
  rw [complex_linear_matrix_column_sum, hMu, sub_self]

/-- Exact homotopy current, with its velocity solved from the full
Jacobian and no external divergence or contour-invariance premise. -/
theorem exact_holomorphic_pullback_current (χ : ι → E → ℂ) (e : ι → E)
    (a x : E) (F : (ι → ℂ) → ℂ)
    (hχ : ∀ i, ContDiffAt ℝ 2 (χ i) x)
    (hF : DifferentiableAt ℂ F (fun i => χ i x))
    (hdet : scalarCoordinateDet χ e x ≠ 0) :
    scalarPartial (fun y => scalarCoordinateDet χ e y * F (fun i => χ i y)) a x -
      (∑ i, scalarPartial (fun y => constructedAngularVelocity χ e a (fun _ _ => 0) i y *
        scalarCoordinateDet χ e y * F (fun j => χ j y)) (e i) x) = 0 := by
  have hdχ (i : ι) : DifferentiableAt ℝ (χ i) x := (hχ i).differentiableAt (by norm_num)
  have hb : DifferentiableAt ℝ (fun y => F (fun i => χ i y)) x :=
    (hF.restrictScalars ℝ).comp x (differentiableAt_pi.mpr hdχ)
  have hc := exact_constructed_regular_current χ e a x (fun _ _ => 0)
    (fun y => F (fun i => χ i y)) hχ (fun _ => differentiableAt_const (0 : ℂ)) hb hdet
  have hz (i : ι) : scalarRegularFrameDerivative χ e (fun _ => (0 : ℂ)) i x = 0 := by
    simp [scalarRegularFrameDerivative, scalarFrameApplied, scalarPartial]
  simpa only [holomorphic_pullback_parameter_derivative_zero χ e a x F hdχ hF hdet,
    zero_mul, Finset.sum_const_zero, hz, add_zero, mul_zero] using hc

theorem matrix_inverse_velocity_zero_sum (M : Matrix ι ι ℂ) (u : ι → ℂ)
    (hdet : M.det ≠ 0) (hM : ∀ j, ∑ i, M i j = 1) (hu : ∑ i, u i = 0) :
    ∑ i, (M⁻¹ *ᵥ u) i = 0 := by
  have he : M *ᵥ (M⁻¹ *ᵥ u) = u := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]
  have hs : (∑ i, (M *ᵥ (M⁻¹ *ᵥ u)) i) = ∑ i, (M⁻¹ *ᵥ u) i := by
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hM, one_mul]
  rw [he, hu] at hs
  exact hs.symm

end IsingBulk.AnisoF002.Isotropic
