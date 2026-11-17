import IsingBulk.AnisoF002.C03.NegativeGaussianMehta

/-!
# Actual Vandermonde radial integration on the independent-coordinate plane

The Gaussian factor is inserted and cancelled inside the proved physical
measure identity.  This transports arbitrary complex radial integrands to
the original real half-line with the exact Mehta/Gamma coefficient.  The
identities are unconditional Bochner change-of-measure identities; later
nonzero period evaluations also establish absolute integrability.
-/

namespace IsingBulk.AnisoF002.NegativeHT.Angular
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem gaussianLaw_integral_weighted_complex (d : ℕ) (f : constrainedPlane d → ℂ) :
    (∫ v, f v ∂gaussianLaw d) =
      (constrainedGaussianIntegral d)⁻¹ •
        ∫ v, gaussianWeight v • f v ∂independentMeasure d := by
  rw [gaussianLaw, integral_smul_measure, gaussianMeasure_mass_exact, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (constrainedGaussianIntegral_pos d).le,
    gaussianMeasure, integral_withDensity_eq_integral_toReal_smul
      (continuous_gaussianWeight d).measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (gaussianWeight_nonneg _)]

theorem gaussianLaw_integral_norm_complex {d : ℕ} (hd : 0 < d) (f : ℝ → ℂ) :
    (∫ v : constrainedPlane d, f ‖v‖ ∂gaussianLaw d) =
      ∫ r : Ioi (0 : ℝ), f r.val ∂radialLaw d := by
  have := gaussianLaw_nullSingleton hd
  have := angularLaw_isProbability hd
  calc
    (∫ v : constrainedPlane d, f ‖v‖ ∂gaussianLaw d) =
        ∫ v : ({0}ᶜ : Set (constrainedPlane d)), f ‖v.val‖
          ∂(gaussianLaw d).comap Subtype.val := by
      rw [integral_subtype_comap (measurableSet_singleton _).compl (fun v => f ‖v‖),
        restrict_compl_singleton]
    _ = ∫ z : AngularSphere d × Ioi (0 : ℝ), f z.2.val
        ∂(angularLaw d).prod (radialLaw d) := by
      simpa only [Function.comp_def, homeomorphUnitSphereProd_apply_snd_coe] using
        (gaussianLaw_polar_measurePreserving hd).integral_comp
          (homeomorphUnitSphereProd (constrainedPlane d)).measurableEmbedding
          (fun z => f z.2.val)
    _ = ∫ r : Ioi (0 : ℝ), f r.val ∂radialLaw d := by
      rw [integral_fun_snd (fun r : Ioi (0 : ℝ) => f r.val)]
      simp

theorem gaussianWeight_cancel_exp {d : ℕ} (v : constrainedPlane d) :
    gaussianWeight v * Real.exp (‖v‖ ^ 2) = planeVandermonde v := by
  unfold gaussianWeight
  calc
    _ = planeVandermonde v * (Real.exp (-‖v‖ ^ 2) * Real.exp (‖v‖ ^ 2)) := by ring
    _ = _ := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

theorem radialLebesgueWeight_cancel_exp (d : ℕ) (r : Ioi (0 : ℝ)) :
    radialLebesgueWeight d r * Real.exp (r.val ^ 2) = r.val ^ radialPower d := by
  unfold radialLebesgueWeight
  rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

theorem radialLaw_integral_cancel_gaussian (d : ℕ) (f : ℝ → ℂ) :
    (∫ r : Ioi (0 : ℝ), Real.exp (r.val ^ 2) • f (r.val ^ 2) ∂radialLaw d) =
      ((1 / 2 : ℝ) * Real.Gamma (radialShape d))⁻¹ •
        ∫ r in Ioi (0 : ℝ), r ^ radialPower d • f (r ^ 2) := by
  rw [radialLaw, integral_smul_measure, ENNReal.toReal_inv, radialWeighted_mass_gamma,
    ENNReal.toReal_ofReal (mul_nonneg (by norm_num)
      (Real.Gamma_pos_of_pos (radialShape_pos d)).le),
    radialWeighted_eq_Lebesgue_density,
    integral_withDensity_eq_integral_toReal_smul
      (continuous_radialLebesgueWeight d).measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (radialLebesgueWeight_pos d _).le, smul_smul,
    radialLebesgueWeight_cancel_exp]
  rw [show (∫ r : Ioi (0 : ℝ), r.val ^ radialPower d • f (r.val ^ 2) ∂positiveLebesgue) =
      ∫ r in Ioi (0 : ℝ), r ^ radialPower d • f (r ^ 2) from
    integral_subtype_comap measurableSet_Ioi (fun r : ℝ => r ^ radialPower d • f (r ^ 2))]

/-- Exact radial integration coefficient for the full physical Vandermonde measure. -/
theorem vandermonde_radial_complex_integral {d : ℕ} (hd : 0 < d) (f : ℝ → ℂ) :
    (∫ v : constrainedPlane d, planeVandermonde v • f (‖v‖ ^ 2) ∂independentMeasure d) =
      (2 * constrainedGaussianIntegral d / Real.Gamma (radialShape d)) •
        ∫ r in Ioi (0 : ℝ), r ^ radialPower d • f (r ^ 2) := by
  have hG : constrainedGaussianIntegral d ≠ 0 := (constrainedGaussianIntegral_pos d).ne'
  have hΓ : Real.Gamma (radialShape d) ≠ 0 := (Real.Gamma_pos_of_pos (radialShape_pos d)).ne'
  calc
    _ = constrainedGaussianIntegral d •
        (∫ v : constrainedPlane d, Real.exp (‖v‖ ^ 2) • f (‖v‖ ^ 2) ∂gaussianLaw d) := by
      rw [gaussianLaw_integral_weighted_complex]
      simp_rw [smul_smul, gaussianWeight_cancel_exp]
      rw [mul_inv_cancel₀ hG, one_smul]
    _ = constrainedGaussianIntegral d •
        (∫ r : Ioi (0 : ℝ), Real.exp (r.val ^ 2) • f (r.val ^ 2) ∂radialLaw d) := by
      rw [gaussianLaw_integral_norm_complex hd (fun r => Real.exp (r ^ 2) • f (r ^ 2))]
    _ = _ := by
      rw [radialLaw_integral_cancel_gaussian, smul_smul]
      congr 1
      field_simp

theorem radial_square_substitution (a : ℕ) (f : ℝ → ℂ) :
    (∫ r in Ioi (0 : ℝ), r ^ (2 * a + 1) • f (r ^ 2)) =
      (1 / 2 : ℝ) • ∫ q in Ioi (0 : ℝ), q ^ a • f q := by
  have h := integral_comp_rpow_Ioi_of_pos
    (g := fun q : ℝ => q ^ a • f q) (show (0 : ℝ) < 2 by norm_num)
  norm_num only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, Real.rpow_two] at h
  have he : (fun r : ℝ => (2 * r) • ((r ^ 2) ^ a • f (r ^ 2))) =
      (fun r => (2 : ℝ) • (r ^ (2 * a + 1) • f (r ^ 2))) := by
    funext r
    rw [smul_smul, smul_smul, ← pow_mul, pow_add, pow_one]
    congr 1
    ring
  rw [he, integral_smul] at h
  rw [← h, smul_smul]
  norm_num

/-- `q=Q` integration, with no missing angular or independent-coordinate normalization. -/
theorem vandermonde_quadratic_complex_integral {d a : ℕ} (hd : 0 < d)
    (ha : radialPower d = 2 * a + 1) (f : ℝ → ℂ) :
    (∫ v : constrainedPlane d, planeVandermonde v • f (‖v‖ ^ 2) ∂independentMeasure d) =
      (constrainedGaussianIntegral d / Real.Gamma (radialShape d)) •
        ∫ q in Ioi (0 : ℝ), q ^ a • f q := by
  rw [vandermonde_radial_complex_integral hd, ha, radial_square_substitution, smul_smul]
  congr 1
  ring

end
end IsingBulk.AnisoF002.NegativeHT.Angular
