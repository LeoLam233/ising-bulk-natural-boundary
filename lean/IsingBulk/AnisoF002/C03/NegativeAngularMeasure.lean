import IsingBulk.AnisoF002.C03.NegativeAngularCoordinates
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# The genuine constrained Vandermonde angular probability law

The reference angular measure is the polar measure of the literal
independent-coordinate Haar measure.  Weighting it by the complete squared
Vandermonde and dividing by its proved positive finite mass defines the
actual law in frozen F002, Lemma 4.2.  No probability-law hypothesis or
concentration estimate is supplied as an assumption.
-/

namespace IsingBulk.AnisoF002.NegativeHT.Angular
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

abbrev AngularSphere (d : ℕ) := Metric.sphere (0 : constrainedPlane d) 1

instance angularSphere_compactSpace (d : ℕ) : CompactSpace (AngularSphere d) :=
  isCompact_iff_compactSpace.mp (isCompact_sphere (0 : constrainedPlane d) 1)

def angularWeight {d : ℕ} (θ : AngularSphere d) : ℝ := planeVandermonde θ.val

theorem continuous_angularWeight (d : ℕ) :
    Continuous (angularWeight : AngularSphere d → ℝ) :=
  (continuous_planeVandermonde d).comp continuous_subtype_val

theorem angularWeight_nonneg {d : ℕ} (θ : AngularSphere d) : 0 ≤ angularWeight θ :=
  planeVandermonde_nonneg θ.val

theorem angular_norm_sq {d : ℕ} (θ : AngularSphere d) :
    ∑ i, (θ.val : Ambient d) i ^ 2 = 1 := by
  rw [← constrained_norm_sq]
  have hθ : ‖θ.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using θ.property
  rw [hθ, one_pow]

theorem exists_angularWeight_pos {d : ℕ} (hd : 0 < d) :
    ∃ θ : AngularSphere d, 0 < angularWeight θ := by
  obtain ⟨v, hv, hpos⟩ := exists_planeVandermonde_pos hd
  have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  let θ : AngularSphere d := ⟨‖v‖⁻¹ • v, by
    rw [Metric.mem_sphere, dist_zero_right]
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ hnorm.ne']⟩
  refine ⟨θ, ?_⟩
  change 0 < planeVandermonde (‖v‖⁻¹ • v)
  rw [planeVandermonde_scaling]
  exact mul_pos (pow_pos (inv_pos.mpr hnorm) _) hpos

def angularSurface (d : ℕ) : Measure (AngularSphere d) :=
  (independentMeasure d).toSphere

instance angularSurface_isFinite (d : ℕ) : IsFiniteMeasure (angularSurface d) := by
  unfold angularSurface
  infer_instance

instance angularSurface_isOpenPos (d : ℕ) : (angularSurface d).IsOpenPosMeasure := by
  unfold angularSurface
  infer_instance

theorem angularWeight_integrable (d : ℕ) :
    Integrable (angularWeight : AngularSphere d → ℝ) (angularSurface d) :=
  (continuous_angularWeight d).integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact

def angularWeighted (d : ℕ) : Measure (AngularSphere d) :=
  (angularSurface d).withDensity (fun θ => ENNReal.ofReal (angularWeight θ))

instance angularWeighted_isFinite (d : ℕ) : IsFiniteMeasure (angularWeighted d) :=
  isFiniteMeasure_withDensity_ofReal (angularWeight_integrable d).hasFiniteIntegral

theorem angularWeighted_mass_pos {d : ℕ} (hd : 0 < d) :
    0 < angularWeighted d univ := by
  obtain ⟨θ, hθ⟩ := exists_angularWeight_pos hd
  have hI : 0 < ∫ θ, angularWeight θ ∂angularSurface d :=
    integral_pos_of_integrable_nonneg_nonzero (continuous_angularWeight d)
      (angularWeight_integrable d) angularWeight_nonneg hθ.ne'
  rw [angularWeighted, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (angularWeight_integrable d)
      (Filter.Eventually.of_forall angularWeight_nonneg)]
  exact ENNReal.ofReal_pos.mpr hI

/-- The actual constrained angular law; its normalization is proved below. -/
def angularLaw (d : ℕ) : Measure (AngularSphere d) :=
  (angularWeighted d univ)⁻¹ • angularWeighted d

theorem angularLaw_isProbability {d : ℕ} (hd : 0 < d) :
    IsProbabilityMeasure (angularLaw d) := by
  refine ⟨?_⟩
  rw [angularLaw, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (angularWeighted_mass_pos hd).ne' (measure_ne_top _ _)

theorem angularLaw_eq_normalized_density (d : ℕ) :
    angularLaw d = (angularWeighted d univ)⁻¹ •
      (independentMeasure d).toSphere.withDensity
        (fun θ : AngularSphere d => ENNReal.ofReal
          (RegularTail.vandermondeSquared (fun i => (θ.val : Ambient d) i))) := rfl

end
end IsingBulk.AnisoF002.NegativeHT.Angular
