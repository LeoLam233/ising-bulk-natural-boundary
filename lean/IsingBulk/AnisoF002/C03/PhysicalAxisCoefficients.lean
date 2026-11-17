import IsingBulk.AnisoF002.C03.PhysicalSeriesAttachment
import IsingBulk.AnisoF002.C03.EndpointCharts

/-!
# Axis exchange for the original complete contour coefficients

The exchange is proved from the literal unsquared polynomial and a
genuine finite double-contour Fubini theorem.  The chosen radius may
differ between the two parameters; proved radius independence removes
that choice before the complete odd and even sums are compared.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open IsingBulk.Anisotropic IsingBulk.Anisotropic.FormFactors
  IsingBulk.AnisoF002.Geometry IsingBulk.First
open scoped BigOperators

theorem physical_spectralS_axis (lam : ℝ) (z : ℂ) :
    spectralS ((lam : ℂ) * z) = spectralT lam z := rfl

theorem physical_spectralT_axis {lam : ℝ} (hlam : lam ≠ 0) (z : ℂ) :
    spectralT lam⁻¹ ((lam : ℂ) * z) = spectralS z := by
  unfold spectralT spectralS
  rw [axis_swap_complex hlam]

theorem physical_spectralA_axis {lam : ℝ} (hlam : lam ≠ 0) (z : ℂ) :
    spectralA lam⁻¹ ((lam : ℂ) * z) = spectralA lam z := by
  unfold spectralA
  rw [axis_swap_complex hlam, mul_comm]

theorem physical_spectralProduct_axis {lam : ℝ} (hlam : lam ≠ 0) (z : ℂ) :
    spectralProduct lam⁻¹ ((lam : ℂ) * z) = spectralProduct lam z := by
  unfold spectralProduct
  rw [physical_spectralT_axis hlam, physical_spectralS_axis, mul_comm]

theorem physical_sliceDispersion_axis {lam : ℝ} (hlam : lam ≠ 0) (z x y : ℂ) :
    sliceDispersion lam⁻¹ ((lam : ℂ) * z) x y = sliceDispersion lam z y x := by
  unfold sliceDispersion dispersionPolynomial
  rw [physical_spectralS_axis, physical_spectralT_axis hlam, physical_spectralA_axis hlam]
  ring

theorem physical_contourAnnulus_axis {lam r : ℝ} {z : ℂ} (hlam : lam ≠ 0)
    (h : ContourAnnulus lam z r) : ContourAnnulus lam⁻¹ ((lam : ℂ) * z) r := by
  refine ⟨h.1, h.2.1, ?_⟩
  intro x y hx hx1 hy hy1
  rw [physical_sliceDispersion_axis hlam]
  exact h.2.2 y x hy hy1 hx hx1

theorem physical_fullDensity_axis {N : ℕ} {lam : ℝ} (hlam : lam ≠ 0)
    (z : ℂ) (x y : Fin N → ℂ) :
    fullDensity lam⁻¹ ((lam : ℂ) * z) x y = fullDensity lam z y x := by
  simp only [fullDensity, IsingBulk.Anisotropic.FormFactors.commonDensity, physical_sliceDispersion_axis hlam]
  ring

theorem physical_fixedCoefficient_axis {N : ℕ} (hN : 0 < N) {lam r : ℝ} {z : ℂ}
    (hlam : lam ≠ 0) (hr : ContourAnnulus lam z r) :
    unscaledFullCoefficientAtRadius N r lam⁻¹ ((lam : ℂ) * z) =
      unscaledFullCoefficientAtRadius N r lam z := by
  unfold unscaledFullCoefficientAtRadius
  simp_rw [physical_fullDensity_axis hlam]
  congr 1
  exact (literal_doubleContour_swap r r (fullDensity lam z)
    (literal_fullDensity_continuous_angles hN hr ⟨le_rfl, hr.2.1⟩ ⟨le_rfl, hr.2.1⟩)).symm

theorem physical_originalCoefficient_axis {N : ℕ} (hN : 0 < N) {lam : ℝ} {z : ℂ}
    (hlam : lam ≠ 0) (hz : z ∉ spectralSetF002 lam) :
    unscaledFullCoefficient N lam⁻¹ ((lam : ℂ) * z) = unscaledFullCoefficient N lam z := by
  have hr := literal_contourRadius_valid hz
  have hzr : (lam : ℂ) * z ∉ spectralSetF002 lam⁻¹ := (axis_swap_spectral_set hlam z).not.mpr hz
  rw [literal_chosenCoefficient_eq_fixed hN hzr (physical_contourAnnulus_axis hlam hr),
    physical_fixedCoefficient_axis hN hlam hr]
  rfl

theorem physical_originalOddSeries_axis {lam : ℝ} {z : ℂ}
    (hlam : lam ≠ 0) (hz : z ∉ spectralSetF002 lam) :
    (∑' n : ℕ, spectralProduct lam⁻¹ ((lam : ℂ) * z) ^ n *
      unscaledFullCoefficient (2 * n + 1) lam⁻¹ ((lam : ℂ) * z)) =
      ∑' n : ℕ, spectralProduct lam z ^ n * unscaledFullCoefficient (2 * n + 1) lam z := by
  apply tsum_congr
  intro n
  rw [physical_spectralProduct_axis hlam, physical_originalCoefficient_axis (by omega) hlam hz]

theorem physical_originalEvenSeries_axis {lam : ℝ} {z : ℂ}
    (hlam : lam ≠ 0) (hz : z ∉ spectralSetF002 lam) :
    (∑' n : ℕ, spectralProduct lam⁻¹ ((lam : ℂ) * z) ^ (n + 1) *
      unscaledFullCoefficient (2 * n + 2) lam⁻¹ ((lam : ℂ) * z)) =
      ∑' n : ℕ, spectralProduct lam z ^ (n + 1) * unscaledFullCoefficient (2 * n + 2) lam z := by
  apply tsum_congr
  intro n
  rw [physical_spectralProduct_axis hlam, physical_originalCoefficient_axis (by omega) hlam hz]

end
end IsingBulk.AnisoF002.RegularTail.C03
