import IsingBulk.AnisoF002.C03.IsotropicActualAnalyticDescendants
import IsingBulk.AnisoF002.C03.IsotropicHolomorphicPullbackCurrent

/-!
# The analytic regular operator equals the actual real-coordinate operator

Complex linearity of the analytic numerator derivative and the full
coordinate inverse prove exact agreement of the regular parameter and
angular frame derivatives. No inverse one-body slope is introduced.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators Matrix
open Set Filter Metric

def regularJointMap {N : ℕ} (χ : Fin N → (ℂ × (Fin N → ℝ)) → ℂ)
    (q : ℂ × (Fin N → ℝ)) : RegularJointSpace N := (q.1, fun i => χ i q)

theorem scalarPartial_joint_holomorphic_comp {N : ℕ}
    (χ : Fin N → (ℂ × (Fin N → ℝ)) → ℂ) (F : RegularJointSpace N → ℂ)
    (x v : ℂ × (Fin N → ℝ))
    (hχ : ∀ i, DifferentiableAt ℝ (χ i) x)
    (hF : DifferentiableAt ℂ F (regularJointMap χ x)) :
    scalarPartial (fun y => F (regularJointMap χ y)) v x =
      fderiv ℂ F (regularJointMap χ x) (v.1, fun i => scalarPartial (χ i) v x) := by
  have hm : DifferentiableAt ℝ (regularJointMap χ) x :=
    differentiableAt_fst.prodMk (differentiableAt_pi.mpr hχ)
  have hd := (hF.hasFDerivAt.restrictScalars ℝ).comp x hm.hasFDerivAt
  simp only [Function.comp_def] at hd
  rw [scalarPartial, hd.fderiv, ContinuousLinearMap.comp_apply]
  have he : fderiv ℝ (regularJointMap χ) x v =
      (v.1, fun i => scalarPartial (χ i) v x) := by
    change fderiv ℝ (fun y : ℂ × (Fin N → ℝ) => (y.1, fun i => χ i y)) x v = _
    rw [DifferentiableAt.fderiv_prodMk differentiableAt_fst (differentiableAt_pi.mpr hχ)]
    apply Prod.ext
    · change fderiv ℝ Prod.fst x v = v.1
      rw [fderiv_fst]
      rfl
    · funext i
      change fderiv ℝ (fun y j => χ j y) x v i = fderiv ℝ (χ i) x v
      rw [fderiv_apply (differentiableAt_pi.mpr hχ) i, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.proj_apply]
  exact congrArg (fun w => fderiv ℂ F (regularJointMap χ x) w) he

theorem joint_complex_linear_column_sum {N : ℕ} (L : RegularJointSpace N →L[ℂ] ℂ)
    (M : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℂ) :
    (∑ j, v j * L (0, fun i => M i j)) = L (0, M *ᵥ v) := by
  exact complex_linear_matrix_column_sum
    (L.comp (ContinuousLinearMap.inr ℂ ℂ (Fin N → ℂ))) M v

theorem scalarRegularFrameDerivative_joint_pullback {N : ℕ}
    (χ : Fin N → (ℂ × (Fin N → ℝ)) → ℂ) (F : RegularJointSpace N → ℂ)
    (x : ℂ × (Fin N → ℝ)) (i : Fin N)
    (hχ : ∀ j, DifferentiableAt ℝ (χ j) x)
    (hF : DifferentiableAt ℂ F (regularJointMap χ x))
    (hdet : scalarCoordinateDet χ actualAngularDirection x ≠ 0) :
    scalarRegularFrameDerivative χ actualAngularDirection
        (fun y => F (regularJointMap χ y)) i x =
      fderiv ℂ F (regularJointMap χ x) (regularComplexAngularDirection i) := by
  let M : Matrix (Fin N) (Fin N) ℂ := scalarCoordinateMatrix χ actualAngularDirection x
  let L := fderiv ℂ F (regularJointMap χ x)
  have hM : M.det ≠ 0 := hdet
  have hcol : M *ᵥ (fun l => M⁻¹ l i) = Pi.single i 1 := by
    funext j
    have hh := congrFun (congrFun (Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hM)) j) i
    simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply, Pi.single_apply,
      eq_comm] using hh
  change (∑ l, M⁻¹ l i * scalarPartial (fun y => F (regularJointMap χ y))
    (actualAngularDirection l) x) = L (regularComplexAngularDirection i)
  simp_rw [scalarPartial_joint_holomorphic_comp χ F x _ hχ hF]
  change (∑ l, M⁻¹ l i * L (0, fun j => M j l)) = L (0, Pi.single i 1)
  rw [joint_complex_linear_column_sum, hcol]

theorem scalarRegularParameterDerivative_joint_pullback {N : ℕ}
    (χ : Fin N → (ℂ × (Fin N → ℝ)) → ℂ) (F : RegularJointSpace N → ℂ)
    (x : ℂ × (Fin N → ℝ))
    (hχ : ∀ j, DifferentiableAt ℝ (χ j) x)
    (hF : DifferentiableAt ℂ F (regularJointMap χ x))
    (hdet : scalarCoordinateDet χ actualAngularDirection x ≠ 0) :
    scalarRegularParameterDerivative χ actualAngularDirection actualTimeDirection
        (fun y => F (regularJointMap χ y)) x =
      fderiv ℂ F (regularJointMap χ x) (regularComplexTimeDirection N) := by
  let M : Matrix (Fin N) (Fin N) ℂ := scalarCoordinateMatrix χ actualAngularDirection x
  let u := fun i => scalarPartial (χ i) actualTimeDirection x
  let L := fderiv ℂ F (regularJointMap χ x)
  have hMu : M *ᵥ (M⁻¹ *ᵥ u) = u := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec]
  change scalarPartial (fun y => F (regularJointMap χ y)) actualTimeDirection x -
    (M⁻¹ *ᵥ u) ⬝ᵥ (fun i => scalarPartial (fun y => F (regularJointMap χ y))
      (actualAngularDirection i) x) = L (regularComplexTimeDirection N)
  simp_rw [scalarPartial_joint_holomorphic_comp χ F x _ hχ hF]
  change L (1, u) - (∑ j, (M⁻¹ *ᵥ u) j * L (0, fun i => M i j)) = L (1, 0)
  rw [joint_complex_linear_column_sum, hMu]
  have he : (1, u) = ((1, 0) : RegularJointSpace N) + (0, u) := by ext <;> simp
  rw [he, map_add, add_sub_cancel_right]

/-- Exact agreement of the full divergence-containing operator. -/
theorem regularTransportAmplitude_joint_pullback {N : ℕ}
    (χ : Fin N → (ℂ × (Fin N → ℝ)) → ℂ)
    (B : RegularJointSpace N → Fin N → ℂ) (F : RegularJointSpace N → ℂ)
    (x : ℂ × (Fin N → ℝ))
    (hχ : ∀ j, DifferentiableAt ℝ (χ j) x)
    (hB : DifferentiableAt ℂ B (regularJointMap χ x))
    (hF : DifferentiableAt ℂ F (regularJointMap χ x))
    (hdet : scalarCoordinateDet χ actualAngularDirection x ≠ 0) :
    regularTransportAmplitude χ actualAngularDirection actualTimeDirection
      (fun i y => B (regularJointMap χ y) i) (fun y => F (regularJointMap χ y)) x =
        analyticTransportAmplitude B F (regularJointMap χ x) := by
  have hBi (i : Fin N) : DifferentiableAt ℂ (fun p => B p i) (regularJointMap χ x) :=
    differentiableAt_pi.mp hB i
  have hdiag (i : Fin N) :
      scalarRegularFrameDerivative χ actualAngularDirection
        (fun y => B (regularJointMap χ y) i) i x =
      fderiv ℂ B (regularJointMap χ x) (regularComplexAngularDirection i) i := by
    rw [scalarRegularFrameDerivative_joint_pullback χ (fun p => B p i) x i hχ (hBi i) hdet,
      fderiv_apply hB i, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  simp only [regularTransportAmplitude, scalarRegularParameterDerivative_joint_pullback χ F x hχ hF hdet,
    scalarRegularFrameDerivative_joint_pullback χ F x _ hχ hF hdet, hdiag,
    analyticTransportAmplitude]

end IsingBulk.AnisoF002.Isotropic
