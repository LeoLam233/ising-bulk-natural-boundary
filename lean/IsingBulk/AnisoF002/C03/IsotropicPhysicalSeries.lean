import IsingBulk.AnisoF002.C03.IsotropicSignedCoefficientJets
import IsingBulk.AnisoF002.C03.PhysicalSeriesAttachment

/-!
# The complete signed isotropic series and the original physical functions

Every odd or even particle is included. The exact finite coefficient
identity transfers to the original full susceptibility series, retaining
the original prefactors and the sinh z normalization. Negative HT uses
the full signed odd series with total angle pi and the single minus sign
proved by the physical angular change of variables.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators ComplexConjugate
open IsingBulk.Anisotropic IsingBulk.Anisotropic.FormFactors
open IsingBulk.AnisoF002.Geometry IsingBulk.AnisoF002.RegularTail.C03

def isotropicFullParticleSeries (m : ℕ) (a : ℝ) (σ S : ℂ) : ℂ :=
  ∑' n : ℕ, isotropicFullParticleCoefficient (m + 2 * n) a σ S

theorem isotropicFullParticleSeries_eq_canonical (m : ℕ) {z : ℂ}
    (h : 0 < (isotropicPhysicalParameter z).im) :
    isotropicFullParticleSeries m 0 1 (isotropicPhysicalParameter z) =
      canonicalAngularTailF002 1 m z := by
  unfold isotropicFullParticleSeries canonicalAngularTailF002
  exact tsum_congr (fun n => isotropicFullParticleCoefficient_eq_canonical (m + 2 * n) h)

theorem isotropic_canonicalTransferFactor {z : ℂ} (h : spectralS z ≠ 0) :
    canonicalTransferFactor 1 z = spectralS z := by
  rw [canonicalTransferFactor, spectralRatioF002, isotropic_spectralT, div_self h,
    Complex.sqrt_one, mul_one]

theorem isotropic_original_high_complete_series {z : ℂ} (hz : z ∈ omegaH 1)
    (h : 0 < (isotropicPhysicalParameter z).im) :
    spectralS z * highNormalizedBulk 1 z =
      highPrefactor 1 z * isotropicFullParticleSeries 0 0 1 (isotropicPhysicalParameter z) := by
  rw [isotropicFullParticleSeries_eq_canonical 0 h,
    ← isotropic_canonicalTransferFactor (isotropicPhysicalParameter_spectralS_ne_zero h)]
  exact original_high_normalized_canonical_identity (by norm_num) hz

theorem isotropic_original_low_complete_series {z : ℂ} (hz : z ∈ omegaL 1)
    (h : 0 < (isotropicPhysicalParameter z).im) :
    lowNormalizedBulk 1 z =
      lowPrefactor 1 z * isotropicFullParticleSeries 1 0 1 (isotropicPhysicalParameter z) := by
  rw [isotropicFullParticleSeries_eq_canonical 1 h]
  exact original_low_normalized_canonical_identity (by norm_num) hz

theorem isotropic_odd_complete_series_neg_conj {S : ℂ} (hS : 0 < S.im) :
    isotropicFullParticleSeries 0 0 1 (-conj S) =
      -conj (isotropicFullParticleSeries 0 Real.pi (-1) S) := by
  unfold isotropicFullParticleSeries
  simp only [zero_add]
  simp_rw [isotropic_odd_coefficient_neg_conj _ hS]
  rw [tsum_neg, ← RCLike.conj_tsum]

theorem isotropic_even_complete_series_neg_conj {S : ℂ} (hS : 0 < S.im) :
    isotropicFullParticleSeries 1 0 1 (-conj S) =
      conj (isotropicFullParticleSeries 1 0 1 S) := by
  unfold isotropicFullParticleSeries
  simp_rw [show ∀ n : ℕ, 1 + 2 * n = 2 * n + 1 from fun _ => by omega,
    isotropic_even_coefficient_neg_conj _ hS]
  exact (RCLike.conj_tsum _).symm

theorem isotropic_original_negative_high_complete_series {z S : ℂ}
    (hz : z ∈ omegaH 1) (hS : 0 < S.im)
    (he : isotropicPhysicalParameter z = -conj S) :
    spectralS z * highNormalizedBulk 1 z =
      -(highPrefactor 1 z * conj (isotropicFullParticleSeries 0 Real.pi (-1) S)) := by
  have hu : 0 < (isotropicPhysicalParameter z).im := by
    rw [he]
    simpa only [Complex.neg_im, Complex.conj_im, neg_neg] using hS
  rw [isotropic_original_high_complete_series hz hu, he,
    isotropic_odd_complete_series_neg_conj hS, mul_neg]

end IsingBulk.AnisoF002.Isotropic
