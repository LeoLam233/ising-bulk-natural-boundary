import IsingBulk.AnisoF002.C03.NegativeVandermondeRadial
import IsingBulk.AnisoF002.C03.NegativeAngularDisplacements

/-!
# Full nonradial polar integration with the actual independent measure

The exact angular law is kept inside the integral.  The constant is the
already evaluated constrained Mehta integral divided by the actual radial
Gamma normalization.  Fubini requires genuine integrability, explicitly
retained here for the later compact physical pole integral.
-/

namespace IsingBulk.AnisoF002.NegativeHT.Angular
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

def complexPlaneEmbedding {d : ℕ} (v : constrainedPlane d) : zeroSumDisplacements (d + 1) :=
  ⟨fun i => ((v : Ambient d) i : ℂ), by
    change angleSum (d + 1) (fun i => ((v : Ambient d) i : ℂ)) = 0
    rw [angleSum_apply, ← Complex.ofReal_sum, constrained_sum, Complex.ofReal_zero]⟩

theorem continuous_complexPlaneEmbedding (d : ℕ) :
    Continuous (complexPlaneEmbedding (d := d)) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  exact Complex.continuous_ofReal.comp
    ((PiLp.continuous_apply 2 (fun _ : Fin (d + 1) => ℝ) i).comp continuous_subtype_val)

theorem complexPlaneEmbedding_square {d : ℕ} (v : constrainedPlane d) :
    displacementSquare (d + 1) (complexPlaneEmbedding v) = ‖v‖ ^ 2 := by
  rw [constrained_norm_sq]
  unfold displacementSquare complexPlaneEmbedding
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem complexPlaneEmbedding_smul_angular {d : ℕ} (r : ℝ) (θ : AngularSphere d) :
    complexPlaneEmbedding (r • θ.val) = angularComplexDisplacement r θ := by
  apply Subtype.ext
  funext i
  rfl

theorem gaussianLaw_integral_polar_complex {d : ℕ} (hd : 0 < d)
    (f : constrainedPlane d → ℂ) :
    (∫ v : constrainedPlane d, f v ∂gaussianLaw d) =
      ∫ z : AngularSphere d × Ioi (0 : ℝ), f (z.2.val • z.1.val)
        ∂(angularLaw d).prod (radialLaw d) := by
  have := gaussianLaw_nullSingleton hd
  let e := homeomorphUnitSphereProd (constrainedPlane d)
  let F : AngularSphere d × Ioi (0 : ℝ) → ℂ := fun z => f (z.2.val • z.1.val)
  calc
    _ = ∫ v : ({0}ᶜ : Set (constrainedPlane d)), f v.val
        ∂(gaussianLaw d).comap Subtype.val := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl f, restrict_compl_singleton]
    _ = ∫ v : ({0}ᶜ : Set (constrainedPlane d)), F (e v)
        ∂(gaussianLaw d).comap Subtype.val := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro v
      have he := congrArg Subtype.val (e.symm_apply_apply v)
      exact (congrArg f he).symm
    _ = _ := (gaussianLaw_polar_measurePreserving hd).integral_comp e.measurableEmbedding F

theorem radialLaw_integral_cancel_gaussian_any (d : ℕ) (f : ℝ → ℂ) :
    (∫ r : Ioi (0 : ℝ), Real.exp (r.val ^ 2) • f r.val ∂radialLaw d) =
      ((1 / 2 : ℝ) * Real.Gamma (radialShape d))⁻¹ •
        ∫ r in Ioi (0 : ℝ), r ^ radialPower d • f r := by
  rw [radialLaw, integral_smul_measure, ENNReal.toReal_inv, radialWeighted_mass_gamma,
    ENNReal.toReal_ofReal (mul_nonneg (by norm_num)
      (Real.Gamma_pos_of_pos (radialShape_pos d)).le),
    radialWeighted_eq_Lebesgue_density,
    integral_withDensity_eq_integral_toReal_smul
      (continuous_radialLebesgueWeight d).measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (radialLebesgueWeight_pos d _).le, smul_smul,
    radialLebesgueWeight_cancel_exp]
  rw [show (∫ r : Ioi (0 : ℝ), r.val ^ radialPower d • f r.val ∂positiveLebesgue) =
      ∫ r in Ioi (0 : ℝ), r ^ radialPower d • f r from
    integral_subtype_comap measurableSet_Ioi (fun r : ℝ => r ^ radialPower d • f r)]

theorem vandermonde_full_polar_integral {d : ℕ} (hd : 0 < d)
    (f : constrainedPlane d → ℂ)
    (hi : Integrable (fun z : AngularSphere d × Ioi (0 : ℝ) =>
      Real.exp (z.2.val ^ 2) • f (z.2.val • z.1.val))
        ((angularLaw d).prod (radialLaw d))) :
    (∫ v : constrainedPlane d, planeVandermonde v • f v ∂independentMeasure d) =
      (2 * constrainedGaussianIntegral d / Real.Gamma (radialShape d)) •
        ∫ r in Ioi (0 : ℝ), r ^ radialPower d •
          (∫ θ : AngularSphere d, f (r • θ.val) ∂angularLaw d) := by
  have := angularLaw_isProbability hd
  have hG : constrainedGaussianIntegral d ≠ 0 := (constrainedGaussianIntegral_pos d).ne'
  have hΓ : Real.Gamma (radialShape d) ≠ 0 := (Real.Gamma_pos_of_pos (radialShape_pos d)).ne'
  have hnorm (θ : AngularSphere d) (r : Ioi (0 : ℝ)) : ‖r.val • θ.val‖ = r.val := by
    have hθ : ‖θ.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using θ.property
    rw [norm_smul, Real.norm_of_nonneg r.property.le, hθ, mul_one]
  calc
    _ = constrainedGaussianIntegral d •
        (∫ v : constrainedPlane d, Real.exp (‖v‖ ^ 2) • f v ∂gaussianLaw d) := by
      rw [gaussianLaw_integral_weighted_complex]
      simp_rw [smul_smul, gaussianWeight_cancel_exp]
      rw [mul_inv_cancel₀ hG, one_smul]
    _ = constrainedGaussianIntegral d •
        (∫ z : AngularSphere d × Ioi (0 : ℝ),
          Real.exp (z.2.val ^ 2) • f (z.2.val • z.1.val)
            ∂(angularLaw d).prod (radialLaw d)) := by
      rw [gaussianLaw_integral_polar_complex hd]
      simp_rw [hnorm]
    _ = constrainedGaussianIntegral d •
        (∫ r : Ioi (0 : ℝ), Real.exp (r.val ^ 2) •
          (∫ θ : AngularSphere d, f (r.val • θ.val) ∂angularLaw d) ∂radialLaw d) := by
      rw [integral_prod_symm _ hi]
      simp_rw [integral_smul]
    _ = _ := by
      rw [radialLaw_integral_cancel_gaussian_any d
        (fun r : ℝ => ∫ θ : AngularSphere d, f (r • θ.val) ∂angularLaw d), smul_smul]
      congr 1
      field_simp

end
end IsingBulk.AnisoF002.NegativeHT.Angular
