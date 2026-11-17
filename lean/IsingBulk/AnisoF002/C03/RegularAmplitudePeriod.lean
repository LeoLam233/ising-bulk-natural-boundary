import IsingBulk.AnisoF002.C03.RegularFirstCoefficientLimit
import IsingBulk.AnisoF002.C03.NegativeComplexQuadraticPeriod

/-!
# The genuine constrained period in the regular first amplitude

The leading collision density is transported through the actual
independent-coordinate chart, not through an orthonormal surface measure.
The finite analytic numerator and its chosen square root remain explicit.
For odd particle numbers, the independently established complex radial
period proves that the complete coefficient amplitude cannot vanish.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open MeasureTheory
open scoped BigOperators
open IsingBulk.AnisoF002.NegativeHT.Angular

theorem independentChart_flat {n : ℕ} (q : Fin n → ℝ) :
    (fun i => (independentChart n q : Ambient n) i) = flatConstrainedAngles q := rfl

theorem edgeVandermondeSquared_real {N : ℕ} (x : Fin N → ℝ) :
    edgeVandermondeSquared (complexAngles x) = (vandermondeSquared x : ℂ) := by
  simp only [edgeVandermondeSquared, vandermondeSquared, complexAngles,
    Complex.ofReal_prod, Complex.ofReal_pow, Complex.ofReal_sub]

theorem quadraticPeriodIntegrand_chart {n k : ℕ} (τ : ℝ) (h : ℂ) (q : Fin n → ℝ) :
    quadraticPeriodIntegrand n k τ h (independentChart n q) =
      edgeVandermondeSquared (complexAngles (flatConstrainedAngles q)) /
        ((τ : ℂ) + h * ∑ i, (flatConstrainedAngles q i : ℂ) ^ 2) ^ k := by
  rw [quadraticPeriodIntegrand, constrained_norm_sq, planeVandermonde,
    independentChart_flat, edgeVandermondeSquared_real]
  simp only [Complex.ofReal_sum, Complex.ofReal_pow]
  rfl

def regularLeadingConstant (b : ℝ) (a : ℂ → ℂ) (n j : ℕ) : ℂ :=
  (2 * edgeCollisionNumerator (affineEdgeCenter b) a ((0 : ℂ), (0 : Fin (n + 1) → ℂ)) /
      deriv upperEdgePhase (b : ℂ)) *
    ((-1 : ℂ) ^ j * (j.factorial : ℂ) * ((n + 1 : ℕ) : ℂ) ^ j) /
      Complex.I ^ (j + 1)

theorem collisionLeadingJet_eq_quadraticPeriod {n : ℕ} (b : ℝ) (a : ℂ → ℂ)
    (j : ℕ) (q : Fin n → ℝ) :
    collisionLeadingJet b a j (flatConstrainedAngles q) =
      regularLeadingConstant b a n j * quadraticPeriodIntegrand n (j + 1)
        ((n + 1 : ℕ) : ℝ) (a 0 / (2 * Complex.I)) (independentChart n q) := by
  rw [quadraticPeriodIntegrand_chart]
  have hden : ((n + 1 : ℕ) : ℂ) * Complex.I +
      a 0 / 2 * ∑ i, (flatConstrainedAngles q i : ℂ) ^ 2 =
        Complex.I * (((n + 1 : ℕ) : ℂ) +
          a 0 / (2 * Complex.I) * ∑ i, (flatConstrainedAngles q i : ℂ) ^ 2) := by
    field_simp
  simp only [collisionLeadingJet, regularLeadingConstant, Complex.ofReal_natCast]
  rw [hden, mul_pow]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem regularLeadingConstant_ne_zero {b : ℝ} {a : ℂ → ℂ}
    (hb : |b| < 1) (ha : 0 < (a 0).im) (n j : ℕ) :
    regularLeadingConstant b a n j ≠ 0 := by
  have ha0 : a 0 ≠ 0 := by intro he; simp [he] at ha
  have hN : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  unfold regularLeadingConstant
  apply div_ne_zero _ (pow_ne_zero _ Complex.I_ne_zero)
  apply mul_ne_zero
  · exact div_ne_zero (mul_ne_zero (by norm_num)
      (edgeCollisionNumerator_center_ne_zero hb ha0)) (upperEdgePhase_deriv_ne_zero hb)
  · exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num))
      (by exact_mod_cast Nat.factorial_ne_zero j)) (pow_ne_zero _ hN)

theorem regularFirstAmplitude_eq_period (b : ℝ) (a : ℂ → ℂ) (n j : ℕ) :
    regularFirstAmplitude b a n j = regularCoefficientNormalization n *
      regularLeadingConstant b a n j *
        ∫ v, quadraticPeriodIntegrand n (j + 1) ((n + 1 : ℕ) : ℝ)
          (a 0 / (2 * Complex.I)) v ∂independentMeasure n := by
  have h := (independentChart_measurePreserving n).integral_comp
    (independentChart n).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (quadraticPeriodIntegrand n (j + 1) ((n + 1 : ℕ) : ℝ) (a 0 / (2 * Complex.I)))
  simp only [regularFirstAmplitude, collisionLeadingJet_eq_quadraticPeriod,
    integral_const_mul, h, mul_assoc]

theorem regularRadialCoefficient_re {a : ℂ → ℂ} :
    (a 0 / (2 * Complex.I)).re = (a 0).im / 2 := by
  norm_num [Complex.div_re, Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring

theorem oddTopOrder_twice (k : ℕ) : oddTopOrder (2 * k + 1) = 2 * k * (k + 1) := by
  have hs : (2 * k + 1) ^ 2 = 2 * (2 * k * (k + 1)) + 1 := by ring
  unfold oddTopOrder
  omega

/-- The full regular coefficient's first amplitude is nonzero for every
odd particle number at least three, with the actual square-root factor
retained and the exact independent-coordinate normalization. -/
theorem regularFirstAmplitude_odd_ne_zero {b : ℝ} {a : ℂ → ℂ}
    (hb : |b| < 1) (ha : 0 < (a 0).im) {k : ℕ} (hk : 0 < k) :
    regularFirstAmplitude b a (2 * k) (oddTopOrder (2 * k + 1)) ≠ 0 := by
  rw [regularFirstAmplitude_eq_period, oddTopOrder_twice]
  apply mul_ne_zero (mul_ne_zero (regularCoefficientNormalization_ne_zero _)
    (regularLeadingConstant_ne_zero hb ha _ _))
  have hp := integral_quadraticPeriod_odd_particles hk 0
    (by positivity : 0 < ((2 * k + 1 : ℕ) : ℝ))
    (by rw [regularRadialCoefficient_re]; exact half_pos ha)
  simp only [Nat.add_zero, Nat.factorial_zero, Nat.cast_one, mul_one, zero_add,
    pow_one] at hp
  rw [hp]
  have hG : (constrainedGaussianIntegral (2 * k) : ℂ) ≠ 0 := by
    exact_mod_cast (constrainedGaussianIntegral_pos (2 * k)).ne'
  have hh : a 0 / (2 * Complex.I) ≠ 0 := by
    apply div_ne_zero
    · intro he; simp [he] at ha
    · exact mul_ne_zero (by norm_num) Complex.I_ne_zero
  exact div_ne_zero hG (mul_ne_zero
    (mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero (2 * k * (k + 1)))
      (pow_ne_zero _ hh)) (by exact_mod_cast (show 2 * k + 1 ≠ 0 by omega)))

end
end IsingBulk.AnisoF002.RegularTail.C03
