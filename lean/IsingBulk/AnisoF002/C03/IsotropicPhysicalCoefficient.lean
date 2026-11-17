import IsingBulk.AnisoF002.C03.IsotropicPhysicalParameter
import IsingBulk.AnisoF002.C03.IsotropicPhysicalDerivativePartition

/-!
# Exact isotropic finite coefficient identification

The actual normalized angular integral is exactly the independent F002
canonical coefficient at lambda=1. The parameter is sinh z+(sinh z)^{-1},
the original independent angular measure is retained, and continuation
to both physical domains uses only the already proved F002 coefficient
identity, never a historical natural-boundary endpoint.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set MeasureTheory
open IsingBulk.Anisotropic IsingBulk.Anisotropic.FormFactors
open IsingBulk.AnisoF002.Geometry IsingBulk.AnisoF002.RegularTail
open IsingBulk.AnisoF002.RegularTail.C03

theorem isotropic_real_density_toroidal {N : ℕ} (S σ : ℂ)
    (k : Fin N → ℤ) (θ : Fin N → ℝ) :
    isotropicBarePhysicalDensity S σ (complexAngles (toroidalTranslation k θ)) =
      isotropicBarePhysicalDensity S σ (complexAngles θ) := by
  have hh := homotopyPulledDensity_toroidal 1 0 0 (isotropicBarePhysicalDensity S σ)
    (isotropicBarePhysicalDensity_periodic S σ) k θ
  unfold complexAngles
  simpa only [homotopyPulledDensity_at_zero] using hh

theorem affineConstraintAngles_zero_eq_flat {n : ℕ} (x : Fin n → ℝ) :
    affineConstraintAngles 0 x = flatConstrainedAngles x := by
  simp only [affineConstraintAngles_eq_snoc, flatConstrainedAngles, zero_sub]

theorem isotropicFullParticleCoefficient_eq_canonical (n : ℕ) {z : ℂ}
    (h : 0 < (isotropicPhysicalParameter z).im) :
    isotropicFullParticleCoefficient n 0 1 (isotropicPhysicalParameter z) =
      canonicalAngularCoefficientF002 1 n z := by
  unfold isotropicFullParticleCoefficient
  rw [angularIntegrationBox_eq_centered_integral _ (fun k x => by
    rw [affineConstraintAngles_toroidal_c03]
    exact isotropic_real_density_toroidal _ _ _ _)]
  have he (x : Fin n → ℝ) :
      isotropicBarePhysicalDensity (isotropicPhysicalParameter z) 1
        (fun i => (affineConstraintAngles 0 x i : ℂ)) =
          isotropicParticleNormalization (n + 1) * canonicalAngularDensityF002 1 z (flatConstrainedAngles x) := by
    rw [affineConstraintAngles_zero_eq_flat]
    exact isotropicPhysicalParameter_canonical_density h _
  simp_rw [he]
  rw [integral_const_mul, canonicalAngularCoefficientF002, regularAngularProbability_integral]
  simp only [isotropicParticleNormalization, Nat.add_sub_cancel, Complex.real_smul,
    one_div, mul_inv_rev]
  push_cast
  ring

theorem isotropicFullParticleCoefficient_eq_original_high (n : ℕ) {z : ℂ}
    (hz : z ∈ omegaH 1) (h : 0 < (isotropicPhysicalParameter z).im) :
    isotropicFullParticleCoefficient n 0 1 (isotropicPhysicalParameter z) =
      spectralS z ^ (n + 1) * unscaledFullCoefficient (n + 1) 1 z := by
  rw [isotropicFullParticleCoefficient_eq_canonical n h,
    canonical_coefficient_eq_original_high n (by norm_num) hz,
    spectralRatioF002, isotropic_spectralT,
    div_self (isotropicPhysicalParameter_spectralS_ne_zero h), Complex.sqrt_one, mul_one]

theorem isotropicFullParticleCoefficient_eq_original_low (n : ℕ) {z : ℂ}
    (hz : z ∈ omegaL 1) (h : 0 < (isotropicPhysicalParameter z).im) :
    isotropicFullParticleCoefficient n 0 1 (isotropicPhysicalParameter z) =
      spectralS z ^ (n + 1) * unscaledFullCoefficient (n + 1) 1 z := by
  rw [isotropicFullParticleCoefficient_eq_canonical n h,
    canonical_coefficient_eq_original_low n (by norm_num) hz,
    spectralRatioF002, isotropic_spectralT,
    div_self (isotropicPhysicalParameter_spectralS_ne_zero h), Complex.sqrt_one, mul_one]

end IsingBulk.AnisoF002.Isotropic
