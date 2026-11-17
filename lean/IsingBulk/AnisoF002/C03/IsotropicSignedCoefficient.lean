import IsingBulk.AnisoF002.C03.IsotropicSignedConjugation

/-!
# Exact signed coefficient conjugation on the original angular box

The independent variables undergo theta -> pi-theta with Jacobian one.
Their full periodic fundamental domain is retained. The constraint is
N pi-a, hence the odd plus coefficient becomes the minus coefficient
with total angle pi; even coefficients keep their original sign.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators ComplexConjugate
open Set MeasureTheory
open IsingBulk.AnisoF002.RegularTail.C03 IsingBulk.AnisoF002.NegativeHT

theorem affineConstraintAngles_shift_reflection {n : ℕ} (a c : ℝ) (x : Fin n → ℝ) :
    affineConstraintAngles ((n + 1 : ℝ) * c - a) (fun i => c - x i) =
      fun i => c - affineConstraintAngles a x i := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [affineConstraintAngles_eq_snoc, Fin.snoc_last, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  · simp only [affineConstraintAngles_eq_snoc, Fin.snoc_castSucc]

theorem original_affine_integral_shift_reflection {n : ℕ}
    (F : (Fin (n + 1) → ℝ) → ℂ) (hF : ∀ k θ, F (toroidalTranslation k θ) = F θ)
    (a c : ℝ) :
    (∫ x in angularIntegrationBox n, F (fun i => c - affineConstraintAngles a x i)) =
      ∫ x in angularIntegrationBox n, F (affineConstraintAngles ((n + 1 : ℝ) * c - a) x) := by
  let G : (Fin n → ℝ) → ℂ := fun x => F (affineConstraintAngles ((n + 1 : ℝ) * c - a) x)
  have hG : ∀ k x, G (toroidalTranslation k x) = G x := by
    intro k x
    dsimp only [G]
    rw [affineConstraintAngles_toroidal_c03, hF]
  have he (x : Fin n → ℝ) : F (fun i => c - affineConstraintAngles a x i) =
      G (fun i => c - x i) := by
    dsimp only [G]
    rw [affineConstraintAngles_shift_reflection]
  simp_rw [he]
  rw [angularIntegrationBox_eq_centered_integral _ ?_,
    angularIntegrationBox_eq_centered_integral G hG]
  · have hf : (fun x : Fin n → ℝ => G (fun i => c - x i)) =
        fun x => G (-x + fun _ => c) := by funext x; congr 1; funext i; simp only [Pi.add_apply, Pi.neg_apply]; ring
    rw [hf, regularAngularBox_integral_reflection (fun x => G (x + fun _ => c))]
    exact regularAngularBox_integral_shift_measurable n G hG _
  · intro k x
    have hh : (fun i => c - toroidalTranslation k x i) =
        toroidalTranslation (fun i => -k i) (fun i => c - x i) := by
      funext i
      simp only [toroidalTranslation, Int.cast_neg]
      ring
    rw [hh, hG]

theorem isotropicFullParticleCoefficient_constraint_period (n : ℕ) (a : ℝ) (σ S : ℂ) (k : ℤ) :
    isotropicFullParticleCoefficient n (a + (k : ℝ) * (2 * Real.pi)) σ S =
      isotropicFullParticleCoefficient n a σ S := by
  unfold isotropicFullParticleCoefficient
  apply setIntegral_congr_fun measurableSet_Icc
  intro x _
  change isotropicBarePhysicalDensity S σ
    (complexAngles (affineConstraintAngles (a + (k : ℝ) * (2 * Real.pi)) x)) =
      isotropicBarePhysicalDensity S σ (complexAngles (affineConstraintAngles a x))
  rw [show a + (k : ℝ) * (2 * Real.pi) = 2 * Real.pi * (k : ℝ) + a by ring,
    affineConstraintAngles_last_period a x k]
  exact isotropic_real_density_toroidal _ _ _ _

theorem isotropicFullParticleCoefficient_neg_conj (n : ℕ) (a : ℝ) (σ : ℂ)
    {S : ℂ} (hS : 0 < S.im) :
    isotropicFullParticleCoefficient n a σ (-conj S) =
      (-1 : ℂ) ^ (n + 1) * conj (isotropicFullParticleCoefficient n
        ((n + 1 : ℝ) * Real.pi - a) ((-1 : ℂ) ^ (n + 1) * conj σ) S) := by
  let σ' := (-1 : ℂ) ^ (n + 1) * conj σ
  have he (x : Fin n → ℝ) :
      isotropicBarePhysicalDensity (-conj S) σ (complexAngles (affineConstraintAngles a x)) =
        (-1 : ℂ) ^ (n + 1) * conj (isotropicBarePhysicalDensity S σ'
          (complexAngles (fun i => Real.pi - affineConstraintAngles a x i))) := by
    have hh := isotropicBarePhysicalDensity_neg_conj hS σ
      (fun i => Real.pi - affineConstraintAngles a x i)
    simpa only [sub_sub_cancel] using hh
  unfold isotropicFullParticleCoefficient
  change (∫ x in angularIntegrationBox n, isotropicBarePhysicalDensity (-conj S) σ
    (complexAngles (affineConstraintAngles a x))) = _
  simp_rw [he]
  rw [integral_const_mul, integral_conj]
  congr 2
  exact original_affine_integral_shift_reflection
    (fun θ => isotropicBarePhysicalDensity S σ' (complexAngles θ))
    (isotropic_real_density_toroidal S σ') a Real.pi

theorem isotropic_odd_coefficient_neg_conj (m : ℕ) {S : ℂ} (hS : 0 < S.im) :
    isotropicFullParticleCoefficient (2 * m) 0 1 (-conj S) =
      -conj (isotropicFullParticleCoefficient (2 * m) Real.pi (-1) S) := by
  rw [isotropicFullParticleCoefficient_neg_conj _ _ _ hS]
  have hn : (-1 : ℂ) ^ (2 * m + 1) = -1 := by simp [pow_add, pow_mul]
  have ha : ((2 * m : ℕ) + 1 : ℝ) * Real.pi - 0 =
      Real.pi + (m : ℤ) * (2 * Real.pi) := by push_cast; ring
  simp only [hn, map_one, mul_one, ha, isotropicFullParticleCoefficient_constraint_period, neg_one_mul]

theorem isotropic_even_coefficient_neg_conj (m : ℕ) {S : ℂ} (hS : 0 < S.im) :
    isotropicFullParticleCoefficient (2 * m + 1) 0 1 (-conj S) =
      conj (isotropicFullParticleCoefficient (2 * m + 1) 0 1 S) := by
  rw [isotropicFullParticleCoefficient_neg_conj _ _ _ hS]
  have hn : (-1 : ℂ) ^ (2 * m + 1 + 1) = 1 := by
    rw [show 2 * m + 1 + 1 = 2 * (m + 1) by omega, pow_mul]
    norm_num
  have ha : ((2 * m + 1 : ℕ) + 1 : ℝ) * Real.pi - 0 =
      0 + ((m : ℤ) + 1) * (2 * Real.pi) := by push_cast; ring
  simp only [hn, map_one, one_mul, ha]
  simpa only [Int.cast_add, Int.cast_one] using
    congrArg conj (isotropicFullParticleCoefficient_constraint_period (2 * m + 1) 0 1 S ((m : ℤ) + 1))

end IsingBulk.AnisoF002.Isotropic
