import IsingBulk.AnisoF002.C03.IsotropicProtectedSecants
import IsingBulk.AnisoF002.RegularTail.PhysicalFactors

/-!
# The actual complete isotropic pair and its retained collision factor

The original canceled pair is identified in regular coordinates. Its
branch fill is then proved equal to one explicit analytic coefficient
times the literal squared coordinate difference. This coefficient uses
the original dispersion, without dividing by a collision difference.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology
open Filter Set

def inversePairOriginal (U : ℂ × ℂ → ℂ) (q : ℂ × ℂ × ℂ) : ℂ :=
  -(Complex.sin ((U (q.1, q.2.1) - U (q.1, q.2.2)) / 2) /
    Complex.sin (((q.2.1 - U (q.1, q.2.1)) + (q.2.2 - U (q.1, q.2.2))) / 2)) ^ 2

def inversePairAlternative (U : ℂ × ℂ → ℂ) (q : ℂ × ℂ × ℂ) : ℂ :=
  -(Complex.sin (((q.2.1 - U (q.1, q.2.1)) - (q.2.2 - U (q.1, q.2.2))) / 2) /
    Complex.sin ((U (q.1, q.2.1) + U (q.1, q.2.2)) / 2)) ^ 2

def inversePairFilled (U : ℂ × ℂ → ℂ) (q : ℂ × ℂ × ℂ) : ℂ :=
  if Complex.sin (((q.2.1 - U (q.1, q.2.1)) + (q.2.2 - U (q.1, q.2.2))) / 2) = 0
  then inversePairAlternative U q else inversePairOriginal U q

def inversePairCollisionCoefficient (U : ℂ × ℂ → ℂ) (q : ℂ × ℂ × ℂ) : ℂ :=
  -(complexSinc ((U (q.1, q.2.1) - U (q.1, q.2.2)) / 2) *
    complexSinc (((q.2.1 - U (q.1, q.2.1)) - (q.2.2 - U (q.1, q.2.2))) / 2) /
      (2 * inverseSecantDenominator U q)) ^ 2

/-- Exact identification with the already checked canceled physical pair
at B=1 on the exponential phase chart, before any branch fill. -/
theorem canceledPair_isotropic_phase (w₁ w₂ φ₁ φ₂ : ℂ) :
    RegularTail.canceledPair 1 (Complex.exp (-(φ₁ * Complex.I)))
      (Complex.exp (-(φ₂ * Complex.I))) (Complex.exp (w₁ * Complex.I))
      (Complex.exp (w₂ * Complex.I)) =
      -(Complex.sin ((w₁ - w₂) / 2) / Complex.sin ((φ₁ + φ₂) / 2)) ^ 2 := by
  rw [RegularTail.canceledPair_eq_sinePair, RegularTail.sinePairCoefficient_exp]
  have he : (φ₁ * Complex.I + φ₂ * Complex.I) / 2 =
      ((φ₁ + φ₂) / 2) * Complex.I := by ring
  rw [he, Complex.sinh_mul_I, mul_pow, Complex.I_sq, div_pow]
  ring

/-- Division-free identity used to retain the collision factor. -/
theorem inverse_pair_sine_difference (S a b wa wb : ℂ)
    (ha : Complex.cos wa + Complex.cos (a - wa) = S)
    (hb : Complex.cos wb + Complex.cos (b - wb) = S) :
    Complex.sin ((wa - wb) / 2) *
        (minusCosineSecant (a - wa) (b - wb) - minusCosineSecant wa wb) =
      ((a - b) * complexSinc ((wa - wb) / 2) *
        complexSinc (((a - wa) - (b - wb)) / 2) / 2) *
          Complex.sin (((a - wa) + (b - wb)) / 2) := by
  have h := inverse_first_secant_difference S a b wa wb ha hb
  rw [← complexSinc_mul ((wa - wb) / 2)]
  unfold minusCosineSecant at *
  linear_combination (complexSinc ((wa - wb) / 2) / 2) * h

theorem inverse_pair_phase_sine_difference (S a b wa wb : ℂ)
    (ha : Complex.cos wa + Complex.cos (a - wa) = S)
    (hb : Complex.cos wb + Complex.cos (b - wb) = S) :
    Complex.sin (((a - wa) - (b - wb)) / 2) *
        (minusCosineSecant (a - wa) (b - wb) - minusCosineSecant wa wb) =
      -((a - b) * complexSinc ((wa - wb) / 2) *
        complexSinc (((a - wa) - (b - wb)) / 2) / 2) *
          Complex.sin ((wa + wb) / 2) := by
  have h := inverse_first_secant_difference S a b wa wb ha hb
  rw [← complexSinc_mul (((a - wa) - (b - wb)) / 2)]
  unfold minusCosineSecant at *
  linear_combination -(complexSinc (((a - wa) - (b - wb)) / 2) / 2) * h

theorem inversePairOriginal_factorization (U : ℂ × ℂ → ℂ) (q : ℂ × ℂ × ℂ)
    (ha : Complex.cos (U (q.1, q.2.1)) +
      Complex.cos (q.2.1 - U (q.1, q.2.1)) = q.1)
    (hb : Complex.cos (U (q.1, q.2.2)) +
      Complex.cos (q.2.2 - U (q.1, q.2.2)) = q.1)
    (hK : inverseSecantDenominator U q ≠ 0)
    (hφ : Complex.sin (((q.2.1 - U (q.1, q.2.1)) +
      (q.2.2 - U (q.1, q.2.2))) / 2) ≠ 0) :
    inversePairOriginal U q = (q.2.1 - q.2.2) ^ 2 * inversePairCollisionCoefficient U q := by
  have h := inverse_pair_sine_difference q.1 q.2.1 q.2.2
    (U (q.1, q.2.1)) (U (q.1, q.2.2)) ha hb
  change Complex.sin ((U (q.1, q.2.1) - U (q.1, q.2.2)) / 2) *
    inverseSecantDenominator U q = _ at h
  have he : Complex.sin ((U (q.1, q.2.1) - U (q.1, q.2.2)) / 2) /
      Complex.sin (((q.2.1 - U (q.1, q.2.1)) + (q.2.2 - U (q.1, q.2.2))) / 2) =
      (q.2.1 - q.2.2) *
        (complexSinc ((U (q.1, q.2.1) - U (q.1, q.2.2)) / 2) *
          complexSinc (((q.2.1 - U (q.1, q.2.1)) - (q.2.2 - U (q.1, q.2.2))) / 2) /
            (2 * inverseSecantDenominator U q)) := by
    field_simp [hK, hφ]
    linear_combination 2 * h
  unfold inversePairOriginal inversePairCollisionCoefficient
  rw [he]
  ring

theorem inversePairAlternative_factorization (U : ℂ × ℂ → ℂ) (q : ℂ × ℂ × ℂ)
    (ha : Complex.cos (U (q.1, q.2.1)) +
      Complex.cos (q.2.1 - U (q.1, q.2.1)) = q.1)
    (hb : Complex.cos (U (q.1, q.2.2)) +
      Complex.cos (q.2.2 - U (q.1, q.2.2)) = q.1)
    (hK : inverseSecantDenominator U q ≠ 0)
    (hw : Complex.sin ((U (q.1, q.2.1) + U (q.1, q.2.2)) / 2) ≠ 0) :
    inversePairAlternative U q = (q.2.1 - q.2.2) ^ 2 * inversePairCollisionCoefficient U q := by
  have h := inverse_pair_phase_sine_difference q.1 q.2.1 q.2.2
    (U (q.1, q.2.1)) (U (q.1, q.2.2)) ha hb
  change Complex.sin (((q.2.1 - U (q.1, q.2.1)) - (q.2.2 - U (q.1, q.2.2))) / 2) *
    inverseSecantDenominator U q = _ at h
  have he : Complex.sin (((q.2.1 - U (q.1, q.2.1)) - (q.2.2 - U (q.1, q.2.2))) / 2) /
      Complex.sin ((U (q.1, q.2.1) + U (q.1, q.2.2)) / 2) =
      -(q.2.1 - q.2.2) *
        (complexSinc ((U (q.1, q.2.1) - U (q.1, q.2.2)) / 2) *
          complexSinc (((q.2.1 - U (q.1, q.2.1)) - (q.2.2 - U (q.1, q.2.2))) / 2) /
            (2 * inverseSecantDenominator U q)) := by
    field_simp [hK, hw]
    linear_combination 2 * h
  unfold inversePairAlternative inversePairCollisionCoefficient
  rw [he]
  ring

/-- A literal collision-square factorization valid even at the double
branch. The alternate expression is used only where the original pair
denominator is zero, and its denominator is proved nonzero there. -/
theorem inversePairFilled_factorization (U : ℂ × ℂ → ℂ) (q : ℂ × ℂ × ℂ)
    (ha : Complex.cos (U (q.1, q.2.1)) +
      Complex.cos (q.2.1 - U (q.1, q.2.1)) = q.1)
    (hb : Complex.cos (U (q.1, q.2.2)) +
      Complex.cos (q.2.2 - U (q.1, q.2.2)) = q.1)
    (hK : inverseSecantDenominator U q ≠ 0) :
    inversePairFilled U q = (q.2.1 - q.2.2) ^ 2 * inversePairCollisionCoefficient U q := by
  unfold inversePairFilled
  split_ifs with hφ
  · apply inversePairAlternative_factorization U q ha hb hK
    intro hw
    apply hK
    simp only [inverseSecantDenominator, minusCosineSecant, hφ, hw, zero_mul, sub_zero]
  · exact inversePairOriginal_factorization U q ha hb hK hφ

theorem inversePairCollisionCoefficient_analyticAt (U : ℂ × ℂ → ℂ) (q : ℂ × ℂ × ℂ)
    (ha : AnalyticAt ℂ U (q.1, q.2.1)) (hb : AnalyticAt ℂ U (q.1, q.2.2))
    (hK : inverseSecantDenominator U q ≠ 0) :
    AnalyticAt ℂ (inversePairCollisionCoefficient U) q := by
  have hS : AnalyticAt ℂ (fun p : ℂ × ℂ × ℂ => p.1) q := analyticAt_fst
  have hA : AnalyticAt ℂ (fun p : ℂ × ℂ × ℂ => p.2.1) q :=
    analyticAt_fst.comp analyticAt_snd
  have hB : AnalyticAt ℂ (fun p : ℂ × ℂ × ℂ => p.2.2) q :=
    analyticAt_snd.comp analyticAt_snd
  have hUa := ha.comp (f := fun p : ℂ × ℂ × ℂ => (p.1, p.2.1)) (hS.prod hA)
  have hUb := hb.comp (f := fun p : ℂ × ℂ × ℂ => (p.1, p.2.2)) (hS.prod hB)
  have hw := (complexSinc_analyticAt _).comp ((hUa.sub hUb).div_const (c := 2))
  have hp := (complexSinc_analyticAt _).comp
    (((hA.sub hUa).sub (hB.sub hUb)).div_const (c := 2))
  exact (((hw.mul hp).div
    (analyticAt_const.mul (inverseSecantDenominator_analyticAt U q ha hb))
    (mul_ne_zero (by norm_num) hK)).pow 2).neg

theorem inversePairFilled_analyticAt (U : ℂ × ℂ → ℂ) (q : ℂ × ℂ × ℂ)
    (ha : AnalyticAt ℂ U (q.1, q.2.1)) (hb : AnalyticAt ℂ U (q.1, q.2.2))
    (hda : ∀ᶠ z in 𝓝 (q.1, q.2.1), Complex.cos (U z) + Complex.cos (z.2 - U z) = z.1)
    (hdb : ∀ᶠ z in 𝓝 (q.1, q.2.2), Complex.cos (U z) + Complex.cos (z.2 - U z) = z.1)
    (hK : inverseSecantDenominator U q ≠ 0) :
    AnalyticAt ℂ (inversePairFilled U) q := by
  have hS : AnalyticAt ℂ (fun p : ℂ × ℂ × ℂ => p.1) q := analyticAt_fst
  have hA : AnalyticAt ℂ (fun p : ℂ × ℂ × ℂ => p.2.1) q :=
    analyticAt_fst.comp analyticAt_snd
  have hB : AnalyticAt ℂ (fun p : ℂ × ℂ × ℂ => p.2.2) q :=
    analyticAt_snd.comp analyticAt_snd
  have hpoly := ((hA.sub hB).pow 2).mul
    (inversePairCollisionCoefficient_analyticAt U q ha hb hK)
  apply hpoly.congr
  filter_upwards [(hS.prod hA).continuousAt.eventually hda,
    (hS.prod hB).continuousAt.eventually hdb,
    (inverseSecantDenominator_analyticAt U q ha hb).continuousAt.eventually_ne hK]
    with p hpa hpb hpK
  exact (inversePairFilled_factorization U p hpa hpb hpK).symm

end IsingBulk.AnisoF002.Isotropic
