import IsingBulk.AnisoF002.C03.NegativeGaussianMomentMajorant

/-!
# F002's uniform constrained angular exponential moment

This proves the actual angular moment of frozen F002 Lemma 4.2 with
`c0 = 1/32`, for every particle number at least three.  It uses the
constructed Vandermonde law, exact independent-coordinate Mehta integral,
actual Gaussian marginal density, complete coordinate sum, and actual
polar product.  The final integration uses a positive Gaussian majorant
on the large-radius event in place of a separate Mills-ratio estimate.
-/

namespace IsingBulk.AnisoF002.NegativeHT.Angular
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

def polarReconstruction {d : ℕ} (z : AngularSphere d × Ioi (0 : ℝ)) : constrainedPlane d :=
  z.2.val • z.1.val

theorem polarReconstruction_measurableEmbedding (d : ℕ) :
    MeasurableEmbedding (polarReconstruction : AngularSphere d × Ioi (0 : ℝ) → constrainedPlane d) := by
  have h := (MeasurableEmbedding.subtype_coe (measurableSet_singleton (0 : constrainedPlane d)).compl).comp
    (homeomorphUnitSphereProd (constrainedPlane d)).symm.measurableEmbedding
  change MeasurableEmbedding (fun z : AngularSphere d × Ioi (0 : ℝ) => z.2.val • z.1.val)
  simpa only [Function.comp_def, homeomorphUnitSphereProd_symm_apply_coe] using h

theorem gaussianLaw_reconstruction_measurePreserving {d : ℕ} (hd : 0 < d) :
    MeasurePreserving (polarReconstruction : AngularSphere d × Ioi (0 : ℝ) → constrainedPlane d)
      ((angularLaw d).prod (radialLaw d)) (gaussianLaw d) := by
  have := gaussianLaw_nullSingleton hd
  have hs : MeasurePreserving (Subtype.val : ({0}ᶜ : Set (constrainedPlane d)) → constrainedPlane d)
      ((gaussianLaw d).comap Subtype.val) (gaussianLaw d) := by
    refine ⟨measurable_subtype_coe, ?_⟩
    rw [map_comap_subtype_coe (measurableSet_singleton _).compl, restrict_compl_singleton]
  have hi := MeasurePreserving.symm
    (homeomorphUnitSphereProd (constrainedPlane d)).toMeasurableEquiv
    (gaussianLaw_polar_measurePreserving hd)
  exact hs.comp hi

def radialLargeSet (d : ℕ) : Set (Ioi (0 : ℝ)) :=
  {r | ((d + 1 : ℕ) : ℝ) ^ 2 / 8 ≤ r.val ^ 2}

theorem measurableSet_radialLargeSet (d : ℕ) : MeasurableSet (radialLargeSet d) := by
  exact (isClosed_le continuous_const (continuous_subtype_val.pow 2)).measurableSet

def radialLargeIndicator (d : ℕ) : Ioi (0 : ℝ) → ℝ :=
  (radialLargeSet d).indicator (fun _ => 1)

theorem radialLargeIndicator_integrable (d : ℕ) : Integrable (radialLargeIndicator d) (radialLaw d) :=
  (integrable_const 1).indicator (measurableSet_radialLargeSet d)

theorem radialLargeIndicator_integral_lower {d : ℕ} (hd : 2 ≤ d) :
    (5 / 8 : ℝ) ≤ ∫ r, radialLargeIndicator d r ∂radialLaw d := by
  rw [radialLargeIndicator, integral_indicator_const 1 (measurableSet_radialLargeSet d),
    smul_eq_mul, mul_one, measureReal_def]
  have h := ENNReal.toReal_mono (measure_ne_top (radialLaw d) (radialLargeSet d))
    (radialLaw_large_quadratic_mass hd)
  simpa only [ENNReal.toReal_div, ENNReal.toReal_ofNat] using h

theorem angular_moment_product_pointwise {d : ℕ} (z : AngularSphere d × Ioi (0 : ℝ)) :
    momentProfile (angularZ z.1) * radialLargeIndicator d z.2 ≤
      gaussianMomentMajorant (polarReconstruction z) := by
  by_cases h : z.2 ∈ radialLargeSet d
  · rw [radialLargeIndicator, Set.indicator_of_mem h, mul_one]
    exact angular_moment_large_radius_pointwise z.1 z.2.val h
  · rw [radialLargeIndicator, Set.indicator_of_notMem h, mul_zero]
    exact gaussianMomentMajorant_nonneg _

def angularMomentConstant : ℝ := (8 / 5 : ℝ) * (momentProfile 128 + gaussianMomentConstant)

theorem angularMomentConstant_pos : 0 < angularMomentConstant := by
  have hp : 0 < momentProfile 128 := by unfold momentProfile; positivity
  unfold angularMomentConstant
  nlinarith [gaussianMomentConstant_nonneg]

/-- The full actual angular exponential moment, with one constant for all `n >= 3`. -/
theorem uniform_angular_exponential_moment {d : ℕ} (hd : 2 ≤ d) :
    (∫ θ : AngularSphere d, (1 + angularZ θ) * Real.exp (angularZ θ / 32) ∂angularLaw d) ≤
      angularMomentConstant := by
  have hd0 : 0 < d := by omega
  have := angularLaw_isProbability hd0
  have hrec := gaussianLaw_reconstruction_measurePreserving hd0
  have hH := gaussianMomentMajorant_integrable hd
  have hprod := (angular_moment_integrable hd0).mul_prod (radialLargeIndicator_integrable d)
  have hmajor := hrec.integrable_comp_of_integrable hH
  have hint := integral_mono hprod hmajor angular_moment_product_pointwise
  rw [integral_prod_mul
    (fun θ : AngularSphere d => momentProfile (angularZ θ)) (radialLargeIndicator d)] at hint
  have htransport := hrec.integral_comp (polarReconstruction_measurableEmbedding d)
    (gaussianMomentMajorant : constrainedPlane d → ℝ)
  change (∫ θ : AngularSphere d, momentProfile (angularZ θ) ∂angularLaw d) *
      (∫ r, radialLargeIndicator d r ∂radialLaw d) ≤
        (∫ z : AngularSphere d × Ioi (0 : ℝ),
          gaussianMomentMajorant (polarReconstruction z) ∂(angularLaw d).prod (radialLaw d)) at hint
  rw [htransport] at hint
  have hupper := hint.trans (gaussianMomentMajorant_integral_le hd)
  have hnonneg : 0 ≤ ∫ θ : AngularSphere d, momentProfile (angularZ θ) ∂angularLaw d :=
    integral_nonneg (fun θ => momentProfile_nonneg (angularZ_nonneg θ))
  have hsmall := mul_le_mul_of_nonneg_left (radialLargeIndicator_integral_lower hd) hnonneg
  change (∫ θ : AngularSphere d, momentProfile (angularZ θ) ∂angularLaw d) ≤ _
  unfold angularMomentConstant
  nlinarith

/-- Frozen F002 Lemma 4.2, including the specified value `c0 = 1/32`. -/
theorem exists_uniform_angular_exponential_moment :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ d : ℕ, 2 ≤ d →
      (∫ θ : AngularSphere d, (1 + angularZ θ) * Real.exp ((1 / 32 : ℝ) * angularZ θ)
        ∂angularLaw d) ≤ C₀ := by
  refine ⟨angularMomentConstant, angularMomentConstant_pos, fun d hd => ?_⟩
  simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm (32 : ℝ)⁻¹] using
    uniform_angular_exponential_moment hd

end
end IsingBulk.AnisoF002.NegativeHT.Angular
