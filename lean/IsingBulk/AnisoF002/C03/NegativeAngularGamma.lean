import IsingBulk.AnisoF002.C03.NegativeAngularRadial
import Mathlib.MeasureTheory.Integral.Gamma

/-!
# Exact Gamma radius and independence for the constrained Gaussian law

The shape is `(n^2 - 1) / 2`, with `n = d + 1`.  All measures here were
constructed from the actual independent-coordinate Gaussian Vandermonde
weight.  The product identity proves radius/angular independence and
does not replace it by an additional probability assumption.
-/

namespace IsingBulk.AnisoF002.NegativeHT.Angular
noncomputable section
open MeasureTheory Set
open scoped ENNReal

def radialShape (d : ℕ) : ℝ := ((radialPower d : ℝ) + 1) / 2

theorem radialShape_pos (d : ℕ) : 0 < radialShape d := by
  unfold radialShape
  positivity

theorem radialShape_exact {d : ℕ} (hd : 0 < d) :
    radialShape d = (((d + 1 : ℕ) : ℝ) ^ 2 - 1) / 2 := by
  have hdeg := RegularTail.vandermonde_degree (d + 1)
  unfold radialShape radialPower
  rw [Nat.cast_add, Nat.cast_sub (Nat.succ_le_iff.mpr hd), Nat.cast_one, Nat.cast_mul,
    Nat.cast_ofNat]
  simp only [Nat.cast_add, Nat.cast_one] at hdeg ⊢
  linarith

theorem radialWeighted_mass_gamma (d : ℕ) :
    radialWeighted d univ = ENNReal.ofReal ((1 / 2 : ℝ) * Real.Gamma (radialShape d)) := by
  rw [radialWeighted_eq_Lebesgue_density, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← ofReal_integral_eq_lintegral_ofReal
      (radialLebesgueWeight_integrable d)
      (Filter.Eventually.of_forall (fun r => (radialLebesgueWeight_pos d r).le))]
  congr 1
  change (∫ r : Ioi (0 : ℝ),
      (fun x : ℝ => x ^ radialPower d * Real.exp (-x ^ 2)) r.val
        ∂volume.comap (Subtype.val : Ioi (0 : ℝ) → ℝ)) = _
  rw [integral_subtype_comap measurableSet_Ioi
    (fun x : ℝ => x ^ radialPower d * Real.exp (-x ^ 2))]
  simpa only [Real.rpow_natCast, Real.rpow_two, radialShape] using
    (integral_rpow_mul_exp_neg_rpow (p := 2) (q := (radialPower d : ℝ))
      (by norm_num) (by have h := Nat.cast_nonneg (α := ℝ) (radialPower d); linarith))

theorem gaussianLaw_polar_measurePreserving {d : ℕ} (hd : 0 < d) :
    MeasurePreserving (homeomorphUnitSphereProd (constrainedPlane d))
      ((gaussianLaw d).comap
        (Subtype.val : ({0}ᶜ : Set (constrainedPlane d)) → constrainedPlane d))
      ((angularLaw d).prod (radialLaw d)) := by
  have hp := gaussian_polar_measurePreserving d
  refine ⟨hp.measurable, ?_⟩
  rw [gaussianLaw, Measure.comap_smul, Measure.map_smul _ hp.measurable.aemeasurable,
    hp.map_eq, gaussianMeasure_mass_factorization hd, angularLaw, radialLaw,
    Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
    ENNReal.mul_inv (Or.inl (angularWeighted_mass_pos hd).ne')
      (Or.inr (radialWeighted_mass_pos d).ne')]

/-- Exact rectangle probabilities for the actual radius and angular variable. -/
theorem gaussianLaw_angular_radial_rectangle {d : ℕ} (hd : 0 < d)
    (s : Set (AngularSphere d)) (t : Set (Ioi (0 : ℝ)))
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    ((gaussianLaw d).comap
      (Subtype.val : ({0}ᶜ : Set (constrainedPlane d)) → constrainedPlane d))
      ((homeomorphUnitSphereProd (constrainedPlane d)) ⁻¹' (s ×ˢ t)) =
      angularLaw d s * radialLaw d t := by
  have := angularLaw_isProbability hd
  have hp := gaussianLaw_polar_measurePreserving hd
  rw [← Measure.map_apply hp.measurable (hs.prod ht), hp.map_eq, Measure.prod_prod]

end
end IsingBulk.AnisoF002.NegativeHT.Angular
