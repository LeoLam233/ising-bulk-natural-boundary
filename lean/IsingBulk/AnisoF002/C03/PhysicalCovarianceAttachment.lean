import IsingBulk.AnisoF002.C03.PhysicalLatticeExchange
import IsingBulk.Anisotropic.Final.Target

/-!
# The unchanged physical covariance and beta fields after finite residues

The original real spin form-factor premise is used only through its literal
fields.  All lattice and particle exchanges come from the preceding F002
contour estimates.  The finite residue identity is explicitly isolated here
and is supplied by its independent construction in the final attachment.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open IsingBulk.Anisotropic IsingBulk.Anisotropic.FormFactors

theorem literal_high_covariance_of_residues {lam x r : ℝ}
    (hlam : 0 < lam) (hx : 0 < x) (hp : realProduct lam x < 1)
    (ha : ContourAnnulus lam (x : ℂ) r)
    (hrep : ∀ N : ℕ, 0 < N → ∀ v : LatticeSite,
      latticeCoefficient N (realB lam x) (realC lam x) v =
        (Real.sqrt (realProduct lam x) : ℂ) ^ N * literalLatticeCoefficientAtRadius N r lam (x : ℂ) v)
    {corrH corrL : ℝ → LatticeSite → ℝ}
    (hphys : PublishedRealSpinFormFactors lam corrH corrL) :
    Summable (corrH x) ∧ highNormalizedBulk lam (x : ℂ) = (highCovarianceSum corrH x : ℂ) := by
  obtain ⟨hs, he⟩ := literal_real_oddSiteSeries hlam hx hp.ne ha hrep
  have hc : Summable (fun v => (corrH x v : ℂ)) := by
    simpa only [hphys.high_spin x hx hp] using hs.mul_left (realHighPrefactor lam x : ℂ)
  refine ⟨Complex.summable_ofReal.mp hc, ?_⟩
  have hcov : (highCovarianceSum corrH x : ℂ) =
      (((1 - realProduct lam x ^ 2) ^ (1 / 4 : ℝ) : ℝ) : ℂ) *
        ∑' n, spectralProduct lam (x : ℂ) ^ n * unscaledFullCoefficient (2 * n + 1) lam (x : ℂ) := by
    unfold highCovarianceSum
    rw [Complex.ofReal_tsum]
    simp_rw [hphys.high_spin x hx hp]
    rw [tsum_mul_left, he]
    have hsqrt : Real.sqrt (realProduct lam x) ≠ 0 :=
      (Real.sqrt_pos.mpr (Physical.realProduct_pos hlam hx)).ne'
    unfold realHighPrefactor
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hsqrt]
  rw [highNormalizedBulk, Physical.highPrefactor_real_normalization hlam hx.le
    ((Physical.realProduct_lt_one_iff_lt_critical hlam hx.le).mp hp)]
  exact hcov.symm

theorem literal_low_covariance_of_residues {lam x r : ℝ}
    (hlam : 0 < lam) (hx : 0 < x) (hp : 1 < realProduct lam x)
    (ha : ContourAnnulus lam (x : ℂ) r)
    (hrep : ∀ N : ℕ, 0 < N → ∀ v : LatticeSite,
      latticeCoefficient N (realB lam x) (realC lam x) v =
        (Real.sqrt (realProduct lam x) : ℂ) ^ N * literalLatticeCoefficientAtRadius N r lam (x : ℂ) v)
    {corrH corrL : ℝ → LatticeSite → ℝ}
    (hphys : PublishedRealSpinFormFactors lam corrH corrL) :
    Summable (fun v : LatticeSite => corrL x v - realMagnetizationSq lam x) ∧
      lowNormalizedBulk lam (x : ℂ) = (lowCovarianceSum lam corrL x : ℂ) := by
  obtain ⟨hs, he⟩ := literal_real_evenSiteSeries hlam hx hp.ne' ha hrep
  have hconn (v : LatticeSite) : ((corrL x v - realMagnetizationSq lam x : ℝ) : ℂ) =
      (realMagnetizationSq lam x : ℂ) * evenSiteSeries lam x v := by
    rw [Complex.ofReal_sub, hphys.low_spin x hx hp]
    ring
  have hc : Summable (fun v : LatticeSite => ((corrL x v - realMagnetizationSq lam x : ℝ) : ℂ)) := by
    simpa only [hconn] using hs.mul_left (realMagnetizationSq lam x : ℂ)
  refine ⟨Complex.summable_ofReal.mp hc, ?_⟩
  rw [lowNormalizedBulk, Physical.lowPrefactor_real_normalization hlam
    ((Physical.critical_lt_iff_realProduct_gt_one hlam hx.le).mpr hp)]
  unfold lowCovarianceSum
  rw [Complex.ofReal_tsum]
  simp_rw [hconn]
  rw [tsum_mul_left, he]

theorem literal_highPhysical_beta {J lam x : ℝ} {corrH : ℝ → LatticeSite → ℝ}
    (h : highNormalizedBulk lam (x : ℂ) = (highCovarianceSum corrH x : ℂ)) :
    highPhysicalBulk J lam (x : ℂ) = (highEnergyFieldResponse J corrH x : ℂ) := by
  simp only [highPhysicalBulk, Pi.mul_apply, inverseTemperature, h, highEnergyFieldResponse]
  push_cast
  rfl

theorem literal_lowPhysical_beta {J lam x : ℝ} {corrL : ℝ → LatticeSite → ℝ}
    (h : lowNormalizedBulk lam (x : ℂ) = (lowCovarianceSum lam corrL x : ℂ)) :
    lowPhysicalBulk J lam (x : ℂ) = (lowEnergyFieldResponse J lam corrL x : ℂ) := by
  simp only [lowPhysicalBulk, Pi.mul_apply, inverseTemperature, h, lowEnergyFieldResponse]
  push_cast
  rfl

theorem literal_realPhysicalIdentification_from_finite_residues (J : ℝ) {lam : ℝ}
    (hlam : 0 < lam) {corrH corrL : ℝ → LatticeSite → ℝ}
    (hphys : PublishedRealSpinFormFactors lam corrH corrL)
    (hfinite : ∀ x : ℝ, 0 < x → realProduct lam x ≠ 1 →
      ∃ r : ℝ, ContourAnnulus lam (x : ℂ) r ∧ ∀ N : ℕ, 0 < N → ∀ v : LatticeSite,
        latticeCoefficient N (realB lam x) (realC lam x) v =
          (Real.sqrt (realProduct lam x) : ℂ) ^ N * literalLatticeCoefficientAtRadius N r lam (x : ℂ) v) :
    RealPhysicalIdentification J lam corrH corrL := by
  constructor
  · intro x hx hp
    obtain ⟨r, hr, hrep⟩ := hfinite x hx hp.ne
    obtain ⟨hs, he⟩ := literal_high_covariance_of_residues hlam hx hp hr hrep hphys
    exact ⟨hs, he, literal_highPhysical_beta he⟩
  · intro x hx hp
    obtain ⟨r, hr, hrep⟩ := hfinite x hx hp.ne'
    obtain ⟨hs, he⟩ := literal_low_covariance_of_residues hlam hx hp hr hrep hphys
    exact ⟨hs, he, literal_lowPhysical_beta he⟩

end
end IsingBulk.AnisoF002.RegularTail.C03
