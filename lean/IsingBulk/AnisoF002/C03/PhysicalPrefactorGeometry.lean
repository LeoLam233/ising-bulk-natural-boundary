import IsingBulk.AnisoF002.C03.DomainBridge
import IsingBulk.AnisoF002.Geometry.LowSimpleConnectivity
import IsingBulk.AnisoF002.Geometry.EndpointCoordinate
import IsingBulk.Anisotropic.FormFactors.ComplexContours
import IsingBulk.Anisotropic.FormFactors.PublishedRealInput

/-!
# Nonzero physical prefactor radicands from F002 geometry

The spectral exclusions are derived from the literal hyperbolic polynomial
identities and the independently checked F002 components.  Only historical
interface definitions occur in these proofs.
-/

namespace IsingBulk.AnisoF002.Physical
noncomputable section
open IsingBulk.Anisotropic IsingBulk.Anisotropic.FormFactors
open Geometry Set

theorem spectralProduct_analytic (lam : ℝ) (z : ℂ) :
    AnalyticAt ℂ (spectralProduct lam) z := by
  exact Complex.analyticAt_sinh.mul
    (Complex.analyticAt_sinh.comp (analyticAt_const.mul analyticAt_id))

theorem spectralProduct_real (lam x : ℝ) :
    spectralProduct lam (x : ℂ) = (realProduct lam x : ℂ) := by
  simp [spectralProduct, spectralS, spectralT, realProduct]

theorem spectral_product_minus_factor (lam : ℝ) (z : ℂ) :
    (spectralA lam z - spectralS z - spectralT lam z) *
      (spectralA lam z + spectralS z + spectralT lam z) =
      (spectralProduct lam z - 1) ^ 2 := by
  simp only [spectralProduct, spectralA, spectralS, spectralT]
  linear_combination (Complex.cosh ((lam : ℂ) * z)) ^ 2 * Complex.cosh_sq_sub_sinh_sq z +
    ((Complex.sinh z) ^ 2 + 1) * Complex.cosh_sq_sub_sinh_sq ((lam : ℂ) * z)

theorem spectral_product_plus_factor (lam : ℝ) (z : ℂ) :
    (spectralA lam z - spectralS z + spectralT lam z) *
      (spectralA lam z + spectralS z - spectralT lam z) =
      (spectralProduct lam z + 1) ^ 2 := by
  simp only [spectralProduct, spectralA, spectralS, spectralT]
  linear_combination (Complex.cosh ((lam : ℂ) * z)) ^ 2 * Complex.cosh_sq_sub_sinh_sq z +
    ((Complex.sinh z) ^ 2 + 1) * Complex.cosh_sq_sub_sinh_sq ((lam : ℂ) * z)

theorem product_sq_one_mem_spectral {lam : ℝ} {z : ℂ}
    (hp : spectralProduct lam z ^ 2 = 1) : z ∈ spectralSetF002 lam := by
  rcases sq_eq_one_iff.mp hp with hp | hp
  · have he := spectral_product_minus_factor lam z
    rw [hp, sub_self, zero_pow two_ne_zero] at he
    rcases mul_eq_zero.mp he with he | he
    · refine ⟨1, by norm_num, 1, by norm_num, ?_⟩
      push_cast
      linear_combination he
    · refine ⟨-1, by norm_num, -1, by norm_num, ?_⟩
      push_cast
      linear_combination he
  · have he := spectral_product_plus_factor lam z
    rw [hp, neg_add_cancel, zero_pow two_ne_zero] at he
    rcases mul_eq_zero.mp he with he | he
    · refine ⟨1, by norm_num, -1, by norm_num, ?_⟩
      push_cast
      linear_combination he
    · refine ⟨-1, by norm_num, 1, by norm_num, ?_⟩
      push_cast
      linear_combination he

theorem high_product_sq_ne_one {lam : ℝ} (hlam : 0 < lam) {z : ℂ}
    (hz : z ∈ omegaH lam) : spectralProduct lam z ^ 2 ≠ 1 := by
  intro hp
  exact omegaHF002_subset_complement hlam hz (product_sq_one_mem_spectral hp)

theorem low_product_sq_ne_one {lam : ℝ} (hlam : 0 < lam) {z : ℂ}
    (hz : z ∈ omegaL lam) : spectralProduct lam z ^ 2 ≠ 1 := by
  intro hp
  exact omegaLF002_subset_complement hlam hz (product_sq_one_mem_spectral hp)

theorem low_product_ne_zero {lam : ℝ} (hlam : 0 < lam) {z : ℂ}
    (hz : z ∈ omegaL lam) : spectralProduct lam z ≠ 0 := by
  have hx : 0 < z.re := lt_of_le_of_lt (lowProfile_nonneg hlam z.im) hz
  apply mul_ne_zero (spectralS_ne_zero_of_re_pos hx)
  exact spectralS_ne_zero_of_re_pos (by
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero] using mul_pos hlam hx)

theorem highRadicand_analytic (lam : ℝ) :
    AnalyticOnNhd ℂ (fun z => 1 - spectralProduct lam z ^ 2) Set.univ :=
  fun z _ => analyticAt_const.sub ((spectralProduct_analytic lam z).pow 2)

theorem highRadicand_ne_zero {lam : ℝ} (hlam : 0 < lam) {z : ℂ}
    (hz : z ∈ omegaH lam) : 1 - spectralProduct lam z ^ 2 ≠ 0 := by
  intro he
  exact high_product_sq_ne_one hlam hz (sub_eq_zero.mp he).symm

theorem lowRadicand_analytic {lam : ℝ} (hlam : 0 < lam) :
    AnalyticOnNhd ℂ (fun z => 1 - (spectralProduct lam z)⁻¹ ^ 2) (omegaL lam) :=
  fun z hz => analyticAt_const.sub
    (((spectralProduct_analytic lam z).inv (low_product_ne_zero hlam hz)).pow 2)

theorem lowRadicand_ne_zero {lam : ℝ} (hlam : 0 < lam) {z : ℂ}
    (hz : z ∈ omegaL lam) : 1 - (spectralProduct lam z)⁻¹ ^ 2 ≠ 0 := by
  intro he
  have hp : (spectralProduct lam z)⁻¹ ^ 2 = 1 := (sub_eq_zero.mp he).symm
  rw [inv_pow, inv_eq_one] at hp
  exact low_product_sq_ne_one hlam hz hp

theorem realProduct_continuous (lam : ℝ) : Continuous (realProduct lam) :=
  Real.continuous_sinh.mul (Real.continuous_sinh.comp (continuous_const.mul continuous_id))

theorem realProduct_nonneg {lam x : ℝ} (hlam : 0 < lam) (hx : 0 ≤ x) :
    0 ≤ realProduct lam x :=
  mul_nonneg (Real.sinh_nonneg_iff.mpr hx) (Real.sinh_nonneg_iff.mpr (mul_nonneg hlam.le hx))

theorem realProduct_pos {lam x : ℝ} (hlam : 0 < lam) (hx : 0 < x) :
    0 < realProduct lam x :=
  mul_pos (Real.sinh_pos_iff.mpr hx) (Real.sinh_pos_iff.mpr (mul_pos hlam hx))

theorem realProduct_strictMonoOn {lam : ℝ} (hlam : 0 < lam) :
    StrictMonoOn (realProduct lam) (Ici (0 : ℝ)) := by
  intro x hx y _ hxy
  have hy : 0 < y := lt_of_le_of_lt hx hxy
  have hs := Real.sinh_strictMono hxy
  have ht := Real.sinh_strictMono (mul_lt_mul_of_pos_left hxy hlam)
  change Real.sinh x * Real.sinh (lam * x) < Real.sinh y * Real.sinh (lam * y)
  calc
    Real.sinh x * Real.sinh (lam * x) ≤ Real.sinh y * Real.sinh (lam * x) :=
      mul_le_mul_of_nonneg_right hs.le
        (Real.sinh_nonneg_iff.mpr (mul_nonneg hlam.le hx))
    _ < Real.sinh y * Real.sinh (lam * y) :=
      mul_lt_mul_of_pos_left ht (Real.sinh_pos_iff.mpr hy)

theorem critical_lt_iff_realProduct_gt_one {lam x : ℝ} (hlam : 0 < lam) (hx : 0 ≤ x) :
    criticalPointF002 lam < x ↔ 1 < realProduct lam x := by
  have hc : criticalPointF002 lam ∈ Ici (0 : ℝ) := (criticalPointF002_pos hlam).le
  have he : realProduct lam (criticalPointF002 lam) = 1 := criticalPointF002_equation hlam
  simpa only [he] using ((realProduct_strictMonoOn hlam).lt_iff_lt hc hx).symm

theorem realProduct_lt_one_iff_lt_critical {lam x : ℝ} (hlam : 0 < lam) (hx : 0 ≤ x) :
    realProduct lam x < 1 ↔ x < criticalPointF002 lam := by
  have hc : criticalPointF002 lam ∈ Ici (0 : ℝ) := (criticalPointF002_pos hlam).le
  have he : realProduct lam (criticalPointF002 lam) = 1 := criticalPointF002_equation hlam
  simpa only [he] using (realProduct_strictMonoOn hlam).lt_iff_lt hx hc

theorem high_real_radicand_pos {lam x : ℝ} (hlam : 0 < lam)
    (hx : 0 ≤ x) (hxc : x < criticalPointF002 lam) : 0 < 1 - realProduct lam x ^ 2 := by
  have hp := (realProduct_lt_one_iff_lt_critical hlam hx).mpr hxc
  have hp0 := realProduct_nonneg hlam hx
  nlinarith

theorem low_real_radicand_pos {lam x : ℝ} (hlam : 0 < lam)
    (hx : criticalPointF002 lam < x) : 0 < 1 - (realProduct lam x)⁻¹ ^ 2 := by
  have hx0 : 0 < x := lt_trans (criticalPointF002_pos hlam) hx
  have hp := (critical_lt_iff_realProduct_gt_one hlam hx0.le).mp hx
  have hp0 : 0 < realProduct lam x := lt_trans zero_lt_one hp
  have hi : 0 < (realProduct lam x)⁻¹ := inv_pos.mpr hp0
  have hi1 : (realProduct lam x)⁻¹ < 1 := (inv_lt_one₀ hp0).mpr hp
  nlinarith

theorem nonnegative_real_mem_high {lam x : ℝ} (hlam : 0 < lam)
    (hx : 0 ≤ x) (hxc : x < criticalPointF002 lam) : (x : ℂ) ∈ omegaH lam := by
  constructor
  · simpa [highStripWidthF002, sliceY] using (highStripWidth_bounds hlam).1
  · change |x| < highProfileF002 lam 0
    rw [abs_of_nonneg hx, highProfile_zero hlam]
    exact hxc

end
end IsingBulk.AnisoF002.Physical
