import IsingBulk.AnisoF002.C03.PhysicalCoefficientContinuation
import IsingBulk.AnisoF002.C03.PhysicalRegularPrefactors

/-!
# Both complete canonical parity sums equal the original physical series

The same single factor S sqrt(T/S) occurs for every odd population.
Every even population has the exact integer spectral-product weight.
The identities concern the full infinite sums on the full original
domains, rather than a restricted particle family or a model series.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open IsingBulk.Anisotropic IsingBulk.Anisotropic.FormFactors
  IsingBulk.AnisoF002.Geometry Set Filter
open scoped Topology BigOperators

def canonicalTransferFactor (lam : ℝ) (z : ℂ) : ℂ :=
  spectralS z * Complex.sqrt (spectralRatioF002 lam z)

theorem canonicalTransferFactor_sq (lam : ℝ) (z : ℂ) :
    canonicalTransferFactor lam z ^ 2 = spectralProduct lam z := by
  unfold canonicalTransferFactor
  rw [mul_pow, show Complex.sqrt (spectralRatioF002 lam z) ^ 2 = spectralRatioF002 lam z from
    edgePrefactor_sq (spectralRatioF002 lam) z]
  unfold spectralRatioF002 spectralProduct
  by_cases hS : spectralS z = 0
  · simp [hS]
  · field_simp

theorem canonicalTransferFactor_odd_power (lam : ℝ) (z : ℂ) (n : ℕ) :
    canonicalTransferFactor lam z ^ (2 * n + 1) =
      canonicalTransferFactor lam z * spectralProduct lam z ^ n := by
  rw [pow_succ, pow_mul, canonicalTransferFactor_sq, mul_comm]

theorem canonicalTransferFactor_even_power (lam : ℝ) (z : ℂ) (n : ℕ) :
    canonicalTransferFactor lam z ^ (2 * n + 2) = spectralProduct lam z ^ (n + 1) := by
  rw [show 2 * n + 2 = 2 * (n + 1) by omega, pow_mul, canonicalTransferFactor_sq]

theorem canonical_odd_series_eq_original {lam : ℝ} {z : ℂ}
    (hlam : 0 < lam) (hz : z ∈ omegaH lam) :
    canonicalAngularTailF002 lam 0 z = canonicalTransferFactor lam z *
      ∑' n : ℕ, spectralProduct lam z ^ n * unscaledFullCoefficient (2 * n + 1) lam z := by
  unfold canonicalAngularTailF002
  simp only [zero_add]
  simp_rw [canonical_coefficient_eq_original_high _ hlam hz]
  change (∑' n : ℕ, canonicalTransferFactor lam z ^ (2 * n + 1) *
    unscaledFullCoefficient (2 * n + 1) lam z) = _
  simp_rw [canonicalTransferFactor_odd_power, mul_assoc]
  rw [tsum_mul_left]

theorem canonical_even_series_eq_original {lam : ℝ} {z : ℂ}
    (hlam : 0 < lam) (hz : z ∈ omegaL lam) :
    canonicalAngularTailF002 lam 1 z =
      ∑' n : ℕ, spectralProduct lam z ^ (n + 1) * unscaledFullCoefficient (2 * n + 2) lam z := by
  unfold canonicalAngularTailF002
  apply tsum_congr
  intro n
  rw [canonical_coefficient_eq_original_low _ hlam hz]
  rw [show 1 + 2 * n + 1 = 2 * n + 2 by omega]
  exact congrArg (fun t => t * unscaledFullCoefficient (2 * n + 2) lam z)
    (canonicalTransferFactor_even_power lam z n)

theorem original_high_normalized_canonical_identity {lam : ℝ} {z : ℂ}
    (hlam : 0 < lam) (hz : z ∈ omegaH lam) :
    canonicalTransferFactor lam z * highNormalizedBulk lam z =
      highPrefactor lam z * canonicalAngularTailF002 lam 0 z := by
  rw [canonical_odd_series_eq_original hlam hz]
  unfold highNormalizedBulk
  ring

theorem original_low_normalized_canonical_identity {lam : ℝ} {z : ℂ}
    (hlam : 0 < lam) (hz : z ∈ omegaL lam) :
    lowNormalizedBulk lam z = lowPrefactor lam z * canonicalAngularTailF002 lam 1 z := by
  rw [canonical_even_series_eq_original hlam hz]
  rfl

theorem canonicalTransferFactor_analyticAt {lam : ℝ} {z : ℂ}
    (hS : spectralS z ≠ 0) (hB : spectralRatioF002 lam z ∈ Complex.slitPlane) :
    AnalyticAt ℂ (canonicalTransferFactor lam) z :=
  (analyticAt_spectralS_f002 z).mul (edgePrefactor_analyticAt (analyticAt_spectralRatioF002 hS) hB)

theorem canonicalTransferFactor_ne_zero {lam : ℝ} {z : ℂ}
    (hp : spectralProduct lam z ≠ 0) : canonicalTransferFactor lam z ≠ 0 := by
  intro he
  have hh := canonicalTransferFactor_sq lam z
  rw [he, zero_pow two_ne_zero] at hh
  exact hp hh.symm

theorem canonicalTransferFactor_analyticAt_regular {lam : ℝ} {z : ℂ}
    (hx : z.re ≠ 0) (hdet : spectralDetF002 lam z ≠ 0) :
    AnalyticAt ℂ (canonicalTransferFactor lam) z := by
  have hS := spectralS_ne_zero_of_re_ne_zero hx
  apply canonicalTransferFactor_analyticAt hS
  apply Or.inr
  rw [spectralRatioF002_im]
  exact div_ne_zero hdet (Complex.normSq_pos.mpr hS).ne'

theorem extension_mul_local_analytic {D : Set ℂ} {f b : ℂ → ℂ} {z : ℂ}
    (hb : AnalyticAt ℂ b z) (he : HasDomainExtension D f z) :
    HasDomainExtension D (b * f) z := by
  obtain ⟨U, hU, hzU, g, hg, heq⟩ := he
  obtain ⟨V, hV, hVopen, hzV⟩ := mem_nhds_iff.mp hb.eventually_analyticAt
  refine ⟨U ∩ V, hU.inter hVopen, ⟨hzU, hzV⟩, b * g, ?_, ?_⟩
  · intro w hw
    exact (hV hw.2).mul (hg w hw.1)
  · intro w hw
    simp only [Pi.mul_apply, heq ⟨hw.1.1, hw.2⟩]

theorem extension_of_local_domain_equality {D : Set ℂ} {f g : ℂ → ℂ} {z : ℂ}
    (hfg : ∀ᶠ w in 𝓝 z, w ∈ D → f w = g w) (he : HasDomainExtension D g z) :
    HasDomainExtension D f z := by
  obtain ⟨U, hU, hzU, h, hh, heq⟩ := he
  obtain ⟨V, hV, hVopen, hzV⟩ := mem_nhds_iff.mp hfg
  refine ⟨U ∩ V, hU.inter hVopen, ⟨hzU, hzV⟩, h, hh.mono inter_subset_left, ?_⟩
  intro w hw
  exact (heq ⟨hw.1.1, hw.2⟩).trans (hV hw.1.2 hw.2).symm

theorem original_high_nonextension_of_canonical {lam : ℝ} {z : ℂ}
    (hlam : 0 < lam) (hz : z ∈ regularBoundaryF002 lam (omegaH lam))
    (hdet : spectralDetF002 lam z ≠ 0)
    (hno : ¬ HasDomainExtension (omegaH lam) (canonicalAngularTailF002 lam 0) z) :
    ¬ HasDomainExtension (omegaH lam) (highNormalizedBulk lam) z := by
  intro he
  have hb := canonicalTransferFactor_analyticAt_regular hz.2.1 hdet
  have hmul := extension_mul_local_analytic hb he
  have hraw : HasDomainExtension (omegaH lam) (highPrefactor lam * canonicalAngularTailF002 lam 0) z := by
    apply extension_of_local_domain_equality (Filter.Eventually.of_forall (fun w hw => ?_)) hmul
    exact (original_high_normalized_canonical_identity hlam hw).symm
  obtain ⟨g, hg, hg0, hge⟩ := Physical.high_regular_prefactor_nonzero_extension hlam hz
  exact hno (Physical.extension_cancel_locally_extended_factor hg hg0 hge hraw)

theorem original_low_nonextension_of_canonical {lam : ℝ} {z : ℂ}
    (hlam : 0 < lam) (hz : z ∈ regularBoundaryF002 lam (omegaL lam))
    (hno : ¬ HasDomainExtension (omegaL lam) (canonicalAngularTailF002 lam 1) z) :
    ¬ HasDomainExtension (omegaL lam) (lowNormalizedBulk lam) z := by
  intro he
  have hraw : HasDomainExtension (omegaL lam) (lowPrefactor lam * canonicalAngularTailF002 lam 1) z := by
    apply extension_of_local_domain_equality (Filter.Eventually.of_forall (fun w hw => ?_)) he
    exact (original_low_normalized_canonical_identity hlam hw).symm
  obtain ⟨g, hg, hg0, hge⟩ := Physical.low_regular_prefactor_nonzero_extension hlam hz
  exact hno (Physical.extension_cancel_locally_extended_factor hg hg0 hge hraw)

end
end IsingBulk.AnisoF002.RegularTail.C03
