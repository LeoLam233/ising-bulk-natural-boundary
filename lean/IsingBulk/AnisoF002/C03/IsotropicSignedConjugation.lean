import IsingBulk.AnisoF002.C03.IsotropicPhysicalCoefficient
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# The actual signed isotropic density under negative conjugation

Both parameters stay in the upper half-plane. The strict-disk root at
(-conj S, pi-theta) is -conj r, proved from the exact reciprocal
polynomial. Every one-body factor changes sign; the complete canceled
pairs conjugate without a sign. Thus the full determinant sign changes
by (-1)^N, with the original normalization retained.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators ComplexConjugate
open IsingBulk.AnisoF002.Geometry IsingBulk.AnisoF002.RegularTail
open IsingBulk.AnisoF002.RegularTail.C03

theorem upperEdgeRoot_neg_conj {W : ℂ} (hW : 0 < W.im) :
    upperEdgeRoot (-conj W) = -conj (upperEdgeRoot W) := by
  apply reciprocal_small_root_unique (upperEdgeRoot_polynomial _) ?_
    (upperEdgeRoot_norm_lt_one (by simpa only [Complex.neg_im, Complex.conj_im, neg_neg] using hW))
    (by simpa only [norm_neg, Complex.norm_conj] using upperEdgeRoot_norm_lt_one hW)
  have hp := congrArg conj (upperEdgeRoot_polynomial W)
  simp only [map_add, map_sub, map_pow, map_mul, map_ofNat, map_one, map_zero] at hp
  linear_combination hp

theorem isotropicDispersion_neg_conj (S : ℂ) (θ : ℝ) :
    isotropicDispersion (-conj S, ((Real.pi - θ : ℝ) : ℂ)) =
      -conj (isotropicDispersion (S, (θ : ℂ))) := by
  simp only [isotropicDispersion, ← Complex.ofReal_cos, Real.cos_pi_sub,
    Complex.ofReal_neg, map_sub, Complex.conj_ofReal]
  ring

theorem isotropicInteriorRoot_neg_conj {S : ℂ} (hS : 0 < S.im) (θ : ℝ) :
    isotropicInteriorRoot (-conj S, ((Real.pi - θ : ℝ) : ℂ)) =
      -conj (isotropicInteriorRoot (S, (θ : ℂ))) := by
  unfold isotropicInteriorRoot
  rw [isotropicDispersion_neg_conj]
  apply upperEdgeRoot_neg_conj
  simpa only [isotropicDispersion, ← Complex.ofReal_cos, Complex.sub_im,
    Complex.ofReal_im, sub_zero] using hS

theorem isotropic_oneBody_neg_conj {S : ℂ} (hS : 0 < S.im) (θ : ℝ) :
    (Complex.sinh (Complex.I * upperPhysicalPhase
      (isotropicDispersion (-conj S, ((Real.pi - θ : ℝ) : ℂ)))))⁻¹ =
      -conj ((Complex.sinh (Complex.I * upperPhysicalPhase
        (isotropicDispersion (S, (θ : ℂ)))))⁻¹) := by
  rw [← isotropic_oneBody_eq_inverse_sinh, ← isotropic_oneBody_eq_inverse_sinh,
    isotropicInteriorRoot_neg_conj hS]
  simp only [map_div₀, map_mul, map_pow, map_sub, map_one, map_ofNat, neg_sq,
    mul_neg, neg_div]

theorem isotropic_canceledPair_neg_conj {S : ℂ} (hS : 0 < S.im) (θ ψ : ℝ) :
    canceledPair 1
      (isotropicInteriorRoot (-conj S, ((Real.pi - θ : ℝ) : ℂ)))
      (isotropicInteriorRoot (-conj S, ((Real.pi - ψ : ℝ) : ℂ)))
      (Complex.exp (((Real.pi - θ : ℝ) : ℂ) * Complex.I))
      (Complex.exp (((Real.pi - ψ : ℝ) : ℂ) * Complex.I)) =
        conj (canceledPair 1 (isotropicInteriorRoot (S, (θ : ℂ)))
          (isotropicInteriorRoot (S, (ψ : ℂ)))
          (Complex.exp ((θ : ℂ) * Complex.I)) (Complex.exp ((ψ : ℂ) * Complex.I))) := by
  rw [canceledPair_eq_sinePair, canceledPair_eq_sinePair,
    isotropicInteriorRoot_neg_conj hS, isotropicInteriorRoot_neg_conj hS]
  have he : (((Real.pi - θ : ℝ) : ℂ) - ((Real.pi - ψ : ℝ) : ℂ)) / 2 =
      -(((θ : ℂ) - (ψ : ℂ)) / 2) := by push_cast; ring
  have hs : conj (Complex.sin (((θ : ℂ) - (ψ : ℂ)) / 2)) =
      Complex.sin (((θ : ℂ) - (ψ : ℂ)) / 2) := by
    rw [show (((θ : ℂ) - (ψ : ℂ)) / 2) = ((θ - ψ) / 2 : ℝ) by push_cast; rfl,
      ← Complex.ofReal_sin, Complex.conj_ofReal]
  simp only [he, Complex.sin_neg, neg_sq, map_mul, map_pow, hs]
  simp only [sinePairCoefficient, map_div₀, map_mul, map_sub, map_pow,
    map_one, map_ofNat, mul_neg, neg_mul, neg_neg]

theorem isotropicParticleNormalization_conj (N : ℕ) :
    conj (isotropicParticleNormalization N) = isotropicParticleNormalization N := by
  simp only [isotropicParticleNormalization, map_inv₀, map_mul, map_pow,
    map_natCast, map_ofNat, Complex.conj_ofReal]

theorem isotropicBarePhysicalDensity_neg_conj {N : ℕ} {S : ℂ}
    (hS : 0 < S.im) (σ : ℂ) (θ : Fin N → ℝ) :
    isotropicBarePhysicalDensity (-conj S) σ (complexAngles (fun i => Real.pi - θ i)) =
      (-1 : ℂ) ^ N * conj (isotropicBarePhysicalDensity S ((-1 : ℂ) ^ N * conj σ)
        (complexAngles θ)) := by
  have hr : (∏ i, isotropicInteriorRoot (-conj S, ((Real.pi - θ i : ℝ) : ℂ))) =
      (-1 : ℂ) ^ N * conj (∏ i, isotropicInteriorRoot (S, (θ i : ℂ))) := by
    simp only [isotropicInteriorRoot_neg_conj hS, Finset.prod_neg,
      Finset.card_univ, Fintype.card_fin, map_prod]
  have hb : (∏ i, (Complex.sinh (Complex.I * upperPhysicalPhase
      (isotropicDispersion (-conj S, ((Real.pi - θ i : ℝ) : ℂ)))))⁻¹) =
      (-1 : ℂ) ^ N * conj (∏ i, (Complex.sinh (Complex.I * upperPhysicalPhase
        (isotropicDispersion (S, (θ i : ℂ)))))⁻¹) := by
    simp only [isotropic_oneBody_neg_conj hS, Finset.prod_neg,
      Finset.card_univ, Fintype.card_fin, map_prod]
  simp only [isotropicBarePhysicalDensity, complexAngles, hr, hb,
    isotropic_canceledPair_neg_conj hS, map_mul, map_div₀, map_add, map_sub, map_prod,
    map_pow, map_neg, map_one, starRingEnd_self_apply, isotropicParticleNormalization_conj]
  ring

end IsingBulk.AnisoF002.Isotropic
