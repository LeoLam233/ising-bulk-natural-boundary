import IsingBulk.AnisoF002.C03.NegativeAngularPolar
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Finite genuine radial law and normalization of the constrained Gaussian

The radial density includes both the independent-coordinate Jacobian
and the exact squared Vandermonde degree.  Its finiteness is established
from an actual Gaussian integral, not imposed as a probability premise.
-/

namespace IsingBulk.AnisoF002.NegativeHT.Angular
noncomputable section
open MeasureTheory Set
open scoped ENNReal

def radialPower (d : ℕ) : ℕ := d - 1 + 2 * (d + 1).choose 2

def positiveLebesgue : Measure (Ioi (0 : ℝ)) :=
  volume.comap (Subtype.val : Ioi (0 : ℝ) → ℝ)

instance positiveLebesgue_isOpenPos : positiveLebesgue.IsOpenPosMeasure :=
  Measure.IsOpenPosMeasure.comap volume (isOpen_Ioi.isOpenEmbedding_subtypeVal)

def radialLebesgueWeight (d : ℕ) (r : Ioi (0 : ℝ)) : ℝ :=
  r.val ^ radialPower d * Real.exp (-r.val ^ 2)

theorem radialLebesgueWeight_pos (d : ℕ) (r : Ioi (0 : ℝ)) :
    0 < radialLebesgueWeight d r :=
  mul_pos (pow_pos r.property _) (Real.exp_pos _)

theorem continuous_radialLebesgueWeight (d : ℕ) : Continuous (radialLebesgueWeight d) := by
  unfold radialLebesgueWeight
  fun_prop

theorem radialWeighted_eq_Lebesgue_density (d : ℕ) :
    radialWeighted d = positiveLebesgue.withDensity
      (fun r => ENNReal.ofReal (radialLebesgueWeight d r)) := by
  unfold radialWeighted Measure.volumeIoiPow
  rw [← withDensity_mul _ (by fun_prop) (continuous_radialWeight d).measurable.ennreal_ofReal]
  congr 1
  funext r
  change ENNReal.ofReal (r.val ^ (d - 1)) * ENNReal.ofReal (radialWeight d r) = _
  rw [← ENNReal.ofReal_mul (pow_nonneg r.property.le _)]
  congr 1
  dsimp [radialWeight, radialLebesgueWeight, radialPower]
  rw [pow_add]
  ring

theorem radialLebesgueWeight_integrable (d : ℕ) :
    Integrable (radialLebesgueWeight d) positiveLebesgue := by
  have h : IntegrableOn (fun x : ℝ => x ^ radialPower d * Real.exp (-x ^ 2)) (Ioi 0) := by
    simpa only [Real.rpow_natCast, neg_mul, one_mul] using
      (integrableOn_rpow_mul_exp_neg_mul_sq (b := 1) zero_lt_one
        (s := (radialPower d : ℝ)) (by have h := Nat.cast_nonneg (α := ℝ) (radialPower d); linarith))
  exact (integrableOn_iff_comap_subtypeVal measurableSet_Ioi).mp h

instance radialWeighted_isFinite (d : ℕ) : IsFiniteMeasure (radialWeighted d) := by
  rw [radialWeighted_eq_Lebesgue_density]
  exact isFiniteMeasure_withDensity_ofReal (radialLebesgueWeight_integrable d).hasFiniteIntegral

theorem radialWeighted_mass_pos (d : ℕ) : 0 < radialWeighted d univ := by
  have hI : 0 < ∫ r, radialLebesgueWeight d r ∂positiveLebesgue :=
    integral_pos_of_integrable_nonneg_nonzero (continuous_radialLebesgueWeight d)
      (radialLebesgueWeight_integrable d) (fun r => (radialLebesgueWeight_pos d r).le)
      (radialLebesgueWeight_pos d ⟨1, by norm_num⟩).ne'
  rw [radialWeighted_eq_Lebesgue_density, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal
      (radialLebesgueWeight_integrable d)
      (Filter.Eventually.of_forall (fun r => (radialLebesgueWeight_pos d r).le))]
  exact ENNReal.ofReal_pos.mpr hI

def radialLaw (d : ℕ) : Measure (Ioi (0 : ℝ)) :=
  (radialWeighted d univ)⁻¹ • radialWeighted d

instance radialLaw_isProbability (d : ℕ) : IsProbabilityMeasure (radialLaw d) := by
  refine ⟨?_⟩
  rw [radialLaw, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (radialWeighted_mass_pos d).ne' (measure_ne_top _ _)

theorem gaussianMeasure_mass_factorization {d : ℕ} (hd : 0 < d) :
    gaussianMeasure d univ = angularWeighted d univ * radialWeighted d univ := by
  obtain ⟨v, hv, _⟩ := exists_planeVandermonde_pos hd
  let : Nontrivial (constrainedPlane d) := ⟨⟨v, 0, hv⟩⟩
  have hzero : gaussianMeasure d {0} = 0 :=
    withDensity_absolutelyContinuous _ _ (measure_singleton 0)
  have hp := gaussian_polar_measurePreserving d
  have hh := congrArg (fun μ : Measure (AngularSphere d × Ioi (0 : ℝ)) => μ univ) hp.map_eq
  rw [Measure.map_apply hp.measurable MeasurableSet.univ, preimage_univ,
    (MeasurableEmbedding.subtype_coe (measurableSet_singleton (0 : constrainedPlane d)).compl).comap_apply,
    image_univ, Subtype.range_coe, measure_compl (measurableSet_singleton _)
      (by rw [hzero]; exact ENNReal.zero_ne_top), hzero, tsub_zero,
    ← univ_prod_univ, Measure.prod_prod] at hh
  exact hh

theorem gaussianMeasure_isFinite {d : ℕ} (hd : 0 < d) :
    IsFiniteMeasure (gaussianMeasure d) := by
  refine ⟨?_⟩
  rw [gaussianMeasure_mass_factorization hd]
  exact ENNReal.mul_lt_top (measure_lt_top _ _) (measure_lt_top _ _)

theorem gaussianMeasure_mass_pos {d : ℕ} (hd : 0 < d) :
    0 < gaussianMeasure d univ := by
  rw [gaussianMeasure_mass_factorization hd]
  exact ENNReal.mul_pos (angularWeighted_mass_pos hd).ne' (radialWeighted_mass_pos d).ne'

def gaussianLaw (d : ℕ) : Measure (constrainedPlane d) :=
  (gaussianMeasure d univ)⁻¹ • gaussianMeasure d

theorem gaussianLaw_isProbability {d : ℕ} (hd : 0 < d) :
    IsProbabilityMeasure (gaussianLaw d) := by
  have := gaussianMeasure_isFinite hd
  refine ⟨?_⟩
  rw [gaussianLaw, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (gaussianMeasure_mass_pos hd).ne' (measure_ne_top _ _)

end
end IsingBulk.AnisoF002.NegativeHT.Angular
