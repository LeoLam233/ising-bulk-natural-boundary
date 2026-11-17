import IsingBulk.AnisoF002.C03.IsotropicFullCircleOneBody
import IsingBulk.AnisoF002.C03.PhysicalCoefficientContinuation
import IsingBulk.AnisoF002.C03.IsotropicFullPhysicalHomotopy

/-!
# The literal isotropic parameter of the original physical temperature

For the original z, s=sinh z and the dispersion is s+s^{-1}. This is
kept distinct from any logarithmic coordinate. The exact unsquared
physical polynomial identifies the same strict-disk root, every one-body
factor and every complete pair in the physical coefficient.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open IsingBulk.Anisotropic IsingBulk.AnisoF002.Geometry
open IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03

def isotropicPhysicalParameter (z : ℂ) : ℂ := Complex.sinh z + (Complex.sinh z)⁻¹

theorem isotropic_spectralT (z : ℂ) : spectralT 1 z = spectralS z := by
  simp only [spectralT, spectralS, Complex.ofReal_one, one_mul]

theorem isotropic_spectralA (z : ℂ) : spectralA 1 z = 1 + spectralS z ^ 2 := by
  simp only [spectralA, spectralS, Complex.ofReal_one, one_mul]
  linear_combination Complex.cosh_sq_sub_sinh_sq z

theorem isotropicPhysicalParameter_spectral (z : ℂ) (hz : spectralS z ≠ 0) :
    spectralS z * isotropicPhysicalParameter z = spectralA 1 z := by
  rw [isotropic_spectralA]
  change Complex.sinh z * (Complex.sinh z + (Complex.sinh z)⁻¹) = 1 + Complex.sinh z ^ 2
  have hz' : Complex.sinh z ≠ 0 := hz
  rw [mul_add, mul_inv_cancel₀ hz']
  ring

theorem isotropicPhysicalParameter_spectralS_ne_zero {z : ℂ}
    (h : 0 < (isotropicPhysicalParameter z).im) : spectralS z ≠ 0 := by
  intro hz
  change Complex.sinh z = 0 at hz
  simp only [isotropicPhysicalParameter, hz, inv_zero, add_zero, Complex.zero_im] at h
  exact (lt_irrefl 0) h

theorem isotropicPhysicalParameter_upper_complement {z : ℂ}
    (h : 0 < (isotropicPhysicalParameter z).im) : z ∉ spectralSetF002 1 := by
  have hs := isotropicPhysicalParameter_spectralS_ne_zero h
  rintro ⟨u, _, v, _, he⟩
  rw [← isotropicPhysicalParameter_spectral z hs, isotropic_spectralT] at he
  have hh : isotropicPhysicalParameter z = (u : ℂ) + (v : ℂ) :=
    mul_left_cancel₀ hs (by simpa only [mul_add] using he)
  have hi := congrArg Complex.im hh
  simp only [Complex.add_im, Complex.ofReal_im, add_zero] at hi
  exact (ne_of_gt h) hi

theorem isotropicPhysicalParameter_dispersion (z w : ℂ) (hz : spectralS z ≠ 0) :
    spectralA 1 z - spectralT 1 z * Complex.cos w =
      spectralS z * isotropicDispersion (isotropicPhysicalParameter z, w) := by
  rw [← isotropicPhysicalParameter_spectral z hz, isotropic_spectralT]
  unfold isotropicDispersion
  ring

theorem isotropicPhysicalParameter_canonical_root {z : ℂ}
    (h : 0 < (isotropicPhysicalParameter z).im) (q : ℝ) :
    spectralSmallRootF002 1 z q = isotropicInteriorRoot (isotropicPhysicalParameter z, (q : ℂ)) := by
  have hz := isotropicPhysicalParameter_upper_complement h
  have hs := isotropicPhysicalParameter_spectralS_ne_zero h
  symm
  apply spectralSmallRootF002_unique q hz
  · unfold spectralRootPolynomialF002
    rw [Complex.ofReal_cos, isotropicPhysicalParameter_dispersion z (q : ℂ) hs]
    have hp := upperEdgeRoot_polynomial (isotropicDispersion (isotropicPhysicalParameter z, (q : ℂ)))
    change spectralS z * upperEdgeRoot _ ^ 2 - 2 * (spectralS z * _) * upperEdgeRoot _ + spectralS z = 0
    linear_combination spectralS z * hp
  · apply upperEdgeRoot_norm_lt_one
    simpa only [isotropicDispersion, ← Complex.ofReal_cos, Complex.sub_im, Complex.ofReal_im,
      sub_zero] using h

theorem isotropic_oneBody_eq_inverse_sinh (S w : ℂ) :
    2 * isotropicInteriorRoot (S, w) / (1 - isotropicInteriorRoot (S, w) ^ 2) =
      (Complex.sinh (Complex.I * upperPhysicalPhase (isotropicDispersion (S, w))))⁻¹ := by
  have hh := oneBody_exp_eq_inv_sinh (upperPhysicalPhase (isotropicDispersion (S, w)) * Complex.I)
  rw [upperPhysicalPhase_exp, one_div] at hh
  simpa only [isotropicInteriorRoot, mul_comm Complex.I] using hh

theorem isotropicPhysicalParameter_canonical_density {N : ℕ} {z : ℂ}
    (h : 0 < (isotropicPhysicalParameter z).im) (q : Fin N → ℝ) :
    isotropicBarePhysicalDensity (isotropicPhysicalParameter z) 1 (complexAngles q) =
      isotropicParticleNormalization N * canonicalAngularDensityF002 1 z q := by
  have hs := isotropicPhysicalParameter_spectralS_ne_zero h
  have hB : spectralRatioF002 1 z = 1 := by
    rw [spectralRatioF002, isotropic_spectralT, div_self hs]
  have hr (i : Fin N) := isotropicPhysicalParameter_canonical_root h (q i)
  have hb (i : Fin N) : spectralOneBodyF002 1 z (q i) =
      (Complex.sinh (Complex.I * upperPhysicalPhase (isotropicDispersion
        (isotropicPhysicalParameter z, (q i : ℂ)))))⁻¹ := by
    rw [spectralOneBodyF002, hr]
    exact isotropic_oneBody_eq_inverse_sinh _ _
  have hp (i j : Fin N) : spectralCanceledPairF002 1 z (q i) (q j) =
      canceledPair 1 (isotropicInteriorRoot (isotropicPhysicalParameter z, (q i : ℂ)))
        (isotropicInteriorRoot (isotropicPhysicalParameter z, (q j : ℂ)))
        (Complex.exp ((q i : ℂ) * Complex.I)) (Complex.exp ((q j : ℂ) * Complex.I)) := by
    rw [spectralCanceledPairF002, isotropic_spectralT, div_self hs, hr, hr]
  simp only [isotropicBarePhysicalDensity, canonicalAngularDensityF002, fullRootNumeratorF002,
    hB, Complex.sqrt_one, one_pow, one_mul, hb, hp, hr, complexAngles]
  ring

end IsingBulk.AnisoF002.Isotropic
