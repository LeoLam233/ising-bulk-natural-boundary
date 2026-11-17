import IsingBulk.AnisoF002.C03.NegativeGaussianCenter
import IsingBulk.AnisoF002.C03.NegativeGaussianRadialExpectation

/-!
# Exact independent-coordinate constrained Mehta normalization

The factorial product and the factor `1 / sqrt n` are derived from the
ordinary Vandermonde integral and the actual center chart.  This is the
normalizing constant of the very same Gaussian measure used to construct
the angular law, including the one-particle base case.
-/

namespace IsingBulk.AnisoF002.NegativeHT.Angular
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem gaussianNorm_pos (n : ℕ) : 0 < gaussianNorm n := by
  unfold gaussianNorm
  exact mul_pos (mul_pos (by positivity) (by exact_mod_cast Nat.factorial_pos n))
    (Real.sqrt_pos.mpr Real.pi_pos)

theorem gaussian_center_scalar (d : ℕ) :
    ((d + 1 : ℕ) : ℝ) * Real.sqrt (Real.pi / ((d + 1 : ℕ) : ℝ)) =
      Real.sqrt Real.pi * Real.sqrt ((d + 1 : ℕ) : ℝ) := by
  have hn : (0 : ℝ) < ((d + 1 : ℕ) : ℝ) := by positivity
  have hs : Real.sqrt ((d + 1 : ℕ) : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hn).ne'
  have hdiv : ((d + 1 : ℕ) : ℝ) / Real.sqrt ((d + 1 : ℕ) : ℝ) =
      Real.sqrt ((d + 1 : ℕ) : ℝ) := by
    apply (div_eq_iff hs).mpr
    simpa only [pow_two] using (Real.sq_sqrt hn.le).symm
  rw [Real.sqrt_div Real.pi_pos.le]
  calc
    ((d + 1 : ℕ) : ℝ) * (Real.sqrt Real.pi / Real.sqrt ((d + 1 : ℕ) : ℝ)) =
        Real.sqrt Real.pi * (((d + 1 : ℕ) : ℝ) / Real.sqrt ((d + 1 : ℕ) : ℝ)) := by ring
    _ = _ := by rw [hdiv]

theorem constrainedGaussianIntegral_full_product (d : ℕ) :
    constrainedGaussianIntegral d =
      ((d + 1).factorial : ℝ) * (∏ i : Fin (d + 1), gaussianNorm i.val) /
        (Real.sqrt Real.pi * Real.sqrt ((d + 1 : ℕ) : ℝ)) := by
  have hi := ordinary_gaussian_vandermonde_integral (d + 1)
  change (∫ x : Fin (d + 1) → ℝ, ordinaryGaussianWeight (d + 1) x) = _ at hi
  rw [gaussian_center_integral_factorization, gaussian_center_scalar] at hi
  apply (eq_div_iff (by positivity)).mpr
  simpa only [mul_comm] using hi

theorem constrainedGaussianIntegral_pos (d : ℕ) : 0 < constrainedGaussianIntegral d := by
  rw [constrainedGaussianIntegral_full_product]
  apply div_pos
  · exact mul_pos (by exact_mod_cast Nat.factorial_pos (d + 1))
      (Finset.prod_pos (fun i _ => gaussianNorm_pos i.val))
  · exact mul_pos (Real.sqrt_pos.mpr Real.pi_pos) (by positivity)

/-- The finite product `P_n = product_(j=1)^(n-1) j! / 2^j`, with `n = d + 1`. -/
def constrainedMehtaProduct (d : ℕ) : ℝ :=
  ∏ i : Fin d, ((i.val + 1).factorial : ℝ) / (2 : ℝ) ^ (i.val + 1)

theorem constrainedMehtaProduct_pos (d : ℕ) : 0 < constrainedMehtaProduct d := by
  apply Finset.prod_pos
  intro i _
  apply div_pos
  · exact_mod_cast Nat.factorial_pos (i.val + 1)
  · positivity

theorem gaussianNorm_shifted_product (d : ℕ) :
    (∏ i : Fin d, gaussianNorm (i.val + 1)) =
      (Real.sqrt Real.pi) ^ d * constrainedMehtaProduct d := by
  unfold gaussianNorm constrainedMehtaProduct
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, Finset.prod_div_distrib, one_div_pow, div_mul_eq_mul_div]
  ring

/-- Frozen F002's constrained Gaussian normalization, with the exact `1/sqrt n`. -/
theorem constrained_gaussian_mehta (d : ℕ) :
    constrainedGaussianIntegral d =
      ((d + 1).factorial : ℝ) * (Real.sqrt Real.pi) ^ d * constrainedMehtaProduct d /
        Real.sqrt ((d + 1 : ℕ) : ℝ) := by
  rw [constrainedGaussianIntegral_full_product, Fin.prod_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, gaussianNorm_shifted_product]
  have h0 : gaussianNorm 0 = Real.sqrt Real.pi := by simp [gaussianNorm]
  rw [h0]
  field_simp

theorem gaussianWeight_integrable (d : ℕ) :
    Integrable (gaussianWeight : constrainedPlane d → ℝ) (independentMeasure d) := by
  exact Integrable.of_integral_ne_zero (constrainedGaussianIntegral_pos d).ne'

theorem gaussianMeasure_mass_exact (d : ℕ) :
    gaussianMeasure d univ = ENNReal.ofReal (constrainedGaussianIntegral d) := by
  rw [gaussianMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (gaussianWeight_integrable d)
      (Filter.Eventually.of_forall gaussianWeight_nonneg)]
  rfl

theorem gaussianLaw_integral_weighted (d : ℕ) (f : constrainedPlane d → ℝ) :
    (∫ v, f v ∂gaussianLaw d) =
      (∫ v, gaussianWeight v * f v ∂independentMeasure d) / constrainedGaussianIntegral d := by
  rw [gaussianLaw, integral_smul_measure, gaussianMeasure_mass_exact, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal (constrainedGaussianIntegral_pos d).le,
    gaussianMeasure, integral_withDensity_eq_integral_toReal_smul
      (continuous_gaussianWeight d).measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (gaussianWeight_nonneg _), smul_eq_mul]
  ring

end
end IsingBulk.AnisoF002.NegativeHT.Angular
