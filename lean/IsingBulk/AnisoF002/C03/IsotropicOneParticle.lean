import IsingBulk.AnisoF002.C03.IsotropicPhysicalSeries

/-!
# The exact physical one-particle coefficients

The zero-dimensional original angular integral has mass one. Its literal
root product kernel and one-body factor simplify using the genuine
reciprocal polynomial; this yields the two rational one-particle terms.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set MeasureTheory
open IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03

theorem isotropic_one_particle_integral (a : ℝ) (σ S : ℂ) :
    isotropicFullParticleCoefficient 0 a σ S =
      ((1 + σ * isotropicInteriorRoot (S, (a : ℂ))) /
        (1 - σ * isotropicInteriorRoot (S, (a : ℂ)))) *
          (2 * isotropicInteriorRoot (S, (a : ℂ)) /
            (1 - isotropicInteriorRoot (S, (a : ℂ)) ^ 2)) := by
  have hpair : indexPairs 1 = ∅ := by decide
  have ha (x : Fin 0 → ℝ) : affineConstraintAngles a x = fun _ => a := by
    funext i
    have hi : i = Fin.last 0 := by apply Fin.ext; omega
    rw [hi, affineConstraintAngles_eq_snoc, Fin.snoc_last]
    simp
  have hbox : angularIntegrationBox 0 = Set.univ := by
    ext x
    simp [angularIntegrationBox]
  unfold isotropicFullParticleCoefficient
  simp_rw [ha]
  simp only [isotropicBarePhysicalDensity, hpair, Finset.prod_empty, mul_one,
    isotropicParticleNormalization]
  norm_num
  rw [← isotropic_oneBody_eq_inverse_sinh, hbox]
  simp [volume_pi, Measure.real]

theorem isotropic_one_particle_plus {S : ℂ} (hS : 0 < S.im) :
    isotropicFullParticleCoefficient 0 0 1 S = (S - 2)⁻¹ := by
  let r := isotropicInteriorRoot (S, 0)
  have hr : ‖r‖ < 1 := upperEdgeRoot_norm_lt_one (by
    simpa only [isotropicDispersion, Complex.cos_zero, Complex.sub_im, Complex.one_im, sub_zero] using hS)
  have hp : r ^ 2 - 2 * (S - 1) * r + 1 = 0 := by
    simpa only [r, isotropicInteriorRoot, isotropicDispersion, Complex.cos_zero] using
      upperEdgeRoot_polynomial (S - 1)
  have hm : 1 - r ≠ 0 := by
    intro he
    have h := sub_eq_zero.mp he
    rw [← h, norm_one] at hr
    exact (lt_irrefl 1) hr
  have hq : 1 - r ^ 2 ≠ 0 := by
    simpa only [pow_two] using pair_root_denominator_ne_zero hr hr
  have hd : S - 2 ≠ 0 := by
    intro he
    have hh := congrArg Complex.im (sub_eq_zero.mp he)
    norm_num at hh
    linarith
  rw [isotropic_one_particle_integral]
  change ((1 + 1 * r) / (1 - 1 * r)) * (2 * r / (1 - r ^ 2)) = (S - 2)⁻¹
  simp only [one_mul]
  field_simp
  linear_combination -(r + 1) * hp

theorem isotropic_one_particle_minus {S : ℂ} (hS : 0 < S.im) :
    isotropicFullParticleCoefficient 0 Real.pi (-1) S = (S + 2)⁻¹ := by
  let r := isotropicInteriorRoot (S, (Real.pi : ℂ))
  have hr : ‖r‖ < 1 := upperEdgeRoot_norm_lt_one (by
    simpa only [isotropicDispersion, Complex.cos_pi, Complex.sub_im,
      Complex.neg_im, Complex.one_im, neg_zero, sub_zero] using hS)
  have hp : r ^ 2 - 2 * (S + 1) * r + 1 = 0 := by
    simpa only [r, isotropicInteriorRoot, isotropicDispersion, Complex.cos_pi, sub_neg_eq_add] using
      upperEdgeRoot_polynomial (S + 1)
  have hm : 1 + r ≠ 0 := by
    intro he
    have h : r = -1 := (eq_neg_iff_add_eq_zero).mpr (by simpa only [add_comm] using he)
    rw [h, norm_neg, norm_one] at hr
    exact (lt_irrefl 1) hr
  have hq : 1 - r ^ 2 ≠ 0 := by
    simpa only [pow_two] using pair_root_denominator_ne_zero hr hr
  have hd : S + 2 ≠ 0 := by
    intro he
    have hh := congrArg Complex.im he
    norm_num at hh
    linarith
  rw [isotropic_one_particle_integral]
  change ((1 + -1 * r) / (1 - -1 * r)) * (2 * r / (1 - r ^ 2)) = (S + 2)⁻¹
  simp only [neg_one_mul, ← sub_eq_add_neg, sub_neg_eq_add]
  field_simp
  linear_combination (r - 1) * hp

end IsingBulk.AnisoF002.Isotropic
