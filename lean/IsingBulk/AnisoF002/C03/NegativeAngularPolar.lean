import IsingBulk.AnisoF002.C03.NegativeAngularMeasure

/-!
# Polar disintegration of the actual constrained Gaussian Vandermonde measure

The independent-coordinate measure is carried by the genuine Euclidean
radius/angular homeomorphism.  The entire Vandermonde degree remains in
the radial factor.  The factorization is a measure identity, before any
normalization, so it preserves the physical independent-coordinate
normalization needed for the later Mehta integral.
-/

namespace IsingBulk.AnisoF002.NegativeHT.Angular
noncomputable section
open MeasureTheory Set
open scoped ENNReal

theorem measurableEquiv_map_withDensity_comp
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (e : X ≃ᵐ Y) (μ : Measure X) (f : Y → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity (fun x => f (e x))).map e = (μ.map e).withDensity f := by
  ext s hs
  rw [e.measurableEmbedding.map_apply, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs, setLIntegral_map hs hf e.measurable]

theorem subtype_comap_withDensity
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (s : Set X)
    (hs : MeasurableSet s) (f : X → ℝ≥0∞) :
    (μ.withDensity f).comap (Subtype.val : s → X) =
      (μ.comap (Subtype.val : s → X)).withDensity (fun x => f x.val) := by
  ext t ht
  rw [(MeasurableEmbedding.subtype_coe hs).comap_apply,
    withDensity_apply _ ((MeasurableEmbedding.subtype_coe hs).measurableSet_image.mpr ht),
    withDensity_apply _ ht, setLIntegral_subtype hs t f]

def gaussianWeight {d : ℕ} (v : constrainedPlane d) : ℝ :=
  Real.exp (-‖v‖ ^ 2) * planeVandermonde v

theorem gaussianWeight_nonneg {d : ℕ} (v : constrainedPlane d) :
    0 ≤ gaussianWeight v := mul_nonneg (Real.exp_nonneg _) (planeVandermonde_nonneg v)

theorem continuous_gaussianWeight (d : ℕ) :
    Continuous (gaussianWeight : constrainedPlane d → ℝ) :=
  (Real.continuous_exp.comp (continuous_norm.pow 2).neg).mul (continuous_planeVandermonde d)

/-- The literal constrained Gaussian weight from F002, on `dv_1 ... dv_d`. -/
def gaussianMeasure (d : ℕ) : Measure (constrainedPlane d) :=
  (independentMeasure d).withDensity (fun v => ENNReal.ofReal (gaussianWeight v))

def radialWeight (d : ℕ) (r : Ioi (0 : ℝ)) : ℝ :=
  Real.exp (-r.val ^ 2) * r.val ^ (2 * (d + 1).choose 2)

theorem radialWeight_nonneg (d : ℕ) (r : Ioi (0 : ℝ)) : 0 ≤ radialWeight d r :=
  mul_nonneg (Real.exp_nonneg _) (pow_nonneg r.property.le _)

theorem continuous_radialWeight (d : ℕ) : Continuous (radialWeight d) := by
  unfold radialWeight
  fun_prop

def radialWeighted (d : ℕ) : Measure (Ioi (0 : ℝ)) :=
  (Measure.volumeIoiPow (d - 1)).withDensity (fun r => ENNReal.ofReal (radialWeight d r))

theorem gaussianWeight_smul_angular {d : ℕ} (θ : AngularSphere d)
    (r : Ioi (0 : ℝ)) :
    gaussianWeight (r.val • θ.val) = angularWeight θ * radialWeight d r := by
  have hθ : ‖θ.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using θ.property
  rw [gaussianWeight, norm_smul, Real.norm_of_nonneg r.property.le, hθ, mul_one,
    planeVandermonde_scaling]
  dsimp [angularWeight, radialWeight]
  ring

/-- Exact unnormalized radius/angle factorization of the physical Gaussian measure. -/
theorem gaussian_polar_measurePreserving (d : ℕ) :
    MeasurePreserving (homeomorphUnitSphereProd (constrainedPlane d))
      ((gaussianMeasure d).comap
        (Subtype.val : ({0}ᶜ : Set (constrainedPlane d)) → constrainedPlane d))
      ((angularWeighted d).prod (radialWeighted d)) := by
  let e := (homeomorphUnitSphereProd (constrainedPlane d)).toMeasurableEquiv
  let f : AngularSphere d × Ioi (0 : ℝ) → ℝ≥0∞ := fun a =>
    ENNReal.ofReal (angularWeight a.1) * ENNReal.ofReal (radialWeight d a.2)
  have hf : Measurable f :=
    ((continuous_angularWeight d).measurable.comp measurable_fst).ennreal_ofReal.mul
      ((continuous_radialWeight d).measurable.comp measurable_snd).ennreal_ofReal
  have hweight : (fun v : ({0}ᶜ : Set (constrainedPlane d)) =>
      ENNReal.ofReal (gaussianWeight v.val)) = fun v => f (e v) := by
    funext v
    have hv : gaussianWeight v.val =
        angularWeight (e v).1 * radialWeight d (e v).2 := by
      have he := (homeomorphUnitSphereProd (constrainedPlane d)).symm_apply_apply v
      have hh := gaussianWeight_smul_angular (e v).1 (e v).2
      have hrec : (e v).2.val • (e v).1.val = v.val :=
        congrArg Subtype.val he
      rw [hrec] at hh
      exact hh
    rw [hv, ENNReal.ofReal_mul (angularWeight_nonneg _)]
  refine ⟨e.measurable, ?_⟩
  change Measure.map e _ = _
  rw [gaussianMeasure, subtype_comap_withDensity _ _ (measurableSet_singleton _).compl,
    hweight, measurableEquiv_map_withDensity_comp e _ f hf]
  have hp := (independentMeasure d).measurePreserving_homeomorphUnitSphereProd
  have hmap : (Measure.comap Subtype.val (independentMeasure d)).map e =
      (angularSurface d).prod (Measure.volumeIoiPow (d - 1)) := by
    simpa only [e, angularSurface, Homeomorph.toMeasurableEquiv_coe,
      constrained_finrank] using hp.map_eq
  rw [hmap]
  exact (prod_withDensity (continuous_angularWeight d).measurable.ennreal_ofReal
    (continuous_radialWeight d).measurable.ennreal_ofReal).symm

end
end IsingBulk.AnisoF002.NegativeHT.Angular
