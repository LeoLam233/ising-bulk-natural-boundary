import IsingBulk.AnisoF002.C03.PhysicalAxisDomains
import IsingBulk.AnisoF002.C03.PhysicalRegularSigns

/-!
# Physical obstruction transfer in the exchanged lattice direction

The original prefactor is kept on its original domain.  Exact contour
axis exchange identifies the complete raw series, while the transformed
canonical series is tested at its actual physical frontier.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open IsingBulk.Anisotropic IsingBulk.Anisotropic.FormFactors
  IsingBulk.AnisoF002.Geometry Set Filter
open scoped Topology

theorem physical_extension_unscale {c z : ℂ} {D E : Set ℂ} {F : ℂ → ℂ}
    (hc : c ≠ 0) (hDE : ∀ w, c * w ∈ E ↔ w ∈ D)
    (he : HasDomainExtension D (fun w => F (c * w)) z) :
    HasDomainExtension E F (c * z) := by
  obtain ⟨U, hU, hzU, g, hg, heq⟩ := he
  refine ⟨(fun w => c⁻¹ * w) ⁻¹' U,
    hU.preimage (continuous_const.mul continuous_id), ?_, (fun w => g (c⁻¹ * w)), ?_, ?_⟩
  · simpa only [mem_preimage, inv_mul_cancel_left₀ hc] using hzU
  · intro w hw
    exact (hg _ hw).comp (f := fun w : ℂ => c⁻¹ * w) (analyticAt_const.mul analyticAt_id)
  · intro w hw
    have hd : c⁻¹ * w ∈ D := (hDE _).mp (by simpa only [mul_inv_cancel_left₀ hc] using hw.2)
    change g (c⁻¹ * w) = F w
    simpa only [mul_inv_cancel_left₀ hc] using heq ⟨hw.1, hd⟩

theorem original_high_normalized_axis_identity {lam : ℝ} {z : ℂ}
    (hlam : 0 < lam) (hz : z ∈ omegaH lam) :
    canonicalTransferFactor lam⁻¹ ((lam : ℂ) * z) * highNormalizedBulk lam z =
      highPrefactor lam z * canonicalAngularTailF002 lam⁻¹ 0 ((lam : ℂ) * z) := by
  rw [canonical_odd_series_eq_original (inv_pos.mpr hlam) ((physical_high_domain_axis hlam z).mpr hz),
    physical_originalOddSeries_axis hlam.ne' (omegaHF002_subset_complement hlam hz)]
  unfold highNormalizedBulk
  ring

theorem original_low_normalized_axis_identity {lam : ℝ} {z : ℂ}
    (hlam : 0 < lam) (hz : z ∈ omegaL lam) :
    lowNormalizedBulk lam z =
      lowPrefactor lam z * canonicalAngularTailF002 lam⁻¹ 1 ((lam : ℂ) * z) := by
  rw [canonical_even_series_eq_original (inv_pos.mpr hlam) ((physical_low_domain_axis hlam z).mpr hz),
    physical_originalEvenSeries_axis hlam.ne' (omegaLF002_subset_complement hlam hz)]
  rfl

theorem original_high_nonextension_of_axis_canonical {lam : ℝ} {z : ℂ}
    (hlam : 0 < lam) (hz : z ∈ regularBoundaryF002 lam (omegaH lam))
    (hdet : spectralDetF002 lam z ≠ 0)
    (hno : ¬ HasDomainExtension (omegaH lam⁻¹)
      (canonicalAngularTailF002 lam⁻¹ 0) ((lam : ℂ) * z)) :
    ¬ HasDomainExtension (omegaH lam) (highNormalizedBulk lam) z := by
  intro he
  have hzr := physical_regularBoundary_axis hlam (physical_high_domain_axis hlam) hz
  have hdc : spectralDetF002 lam⁻¹ ((lam : ℂ) * z) ≠ 0 := by
    rw [axis_swap_determinant hlam.ne']
    exact neg_ne_zero.mpr hdet
  have hb := (canonicalTransferFactor_analyticAt_regular hzr.2.1 hdc).comp
    (f := fun w : ℂ => (lam : ℂ) * w) (analyticAt_const.mul analyticAt_id)
  have hmul := extension_mul_local_analytic hb he
  have hraw : HasDomainExtension (omegaH lam)
      (highPrefactor lam * fun w => canonicalAngularTailF002 lam⁻¹ 0 ((lam : ℂ) * w)) z := by
    apply extension_of_local_domain_equality (Filter.Eventually.of_forall (fun w hw => ?_)) hmul
    exact (original_high_normalized_axis_identity hlam hw).symm
  obtain ⟨g, hg, hg0, hge⟩ := Physical.high_regular_prefactor_nonzero_extension hlam hz
  have hc := Physical.extension_cancel_locally_extended_factor hg hg0 hge hraw
  exact hno (physical_extension_unscale (Complex.ofReal_ne_zero.mpr hlam.ne')
    (physical_high_domain_axis hlam) hc)

theorem original_low_nonextension_of_axis_canonical {lam : ℝ} {z : ℂ}
    (hlam : 0 < lam) (hz : z ∈ regularBoundaryF002 lam (omegaL lam))
    (hno : ¬ HasDomainExtension (omegaL lam⁻¹)
      (canonicalAngularTailF002 lam⁻¹ 1) ((lam : ℂ) * z)) :
    ¬ HasDomainExtension (omegaL lam) (lowNormalizedBulk lam) z := by
  intro he
  have hraw : HasDomainExtension (omegaL lam)
      (lowPrefactor lam * fun w => canonicalAngularTailF002 lam⁻¹ 1 ((lam : ℂ) * w)) z := by
    apply extension_of_local_domain_equality (Filter.Eventually.of_forall (fun w hw => ?_)) he
    exact (original_low_normalized_axis_identity hlam hw).symm
  obtain ⟨g, hg, hg0, hge⟩ := Physical.low_regular_prefactor_nonzero_extension hlam hz
  have hc := Physical.extension_cancel_locally_extended_factor hg hg0 hge hraw
  exact hno (physical_extension_unscale (Complex.ofReal_ne_zero.mpr hlam.ne')
    (physical_low_domain_axis hlam) hc)

theorem positive_regular_second_high_rational_obstruction {lam : ℝ} {z : ℂ} {r p : ℕ}
    (hlam : 0 < lam) (hz : z ∈ regularBoundaryF002 lam (omegaH lam))
    (hr : 0 < r) (hrp : 2 * r < p) (hcop : r.Coprime p) (hp : Odd p)
    (hinc : spectralA lam z = spectralS z + spectralT lam z * (Real.cos (regularRationalAngle r p) : ℂ))
    (hdet : spectralDetF002 lam z ≠ 0) :
    ¬ HasDomainExtension (omegaH lam) (highNormalizedBulk lam) z := by
  apply original_high_nonextension_of_axis_canonical hlam hz hdet
  have hzr := physical_regularBoundary_axis hlam (physical_high_domain_axis hlam) hz
  have hc : spectralA lam⁻¹ ((lam : ℂ) * z) =
      spectralS ((lam : ℂ) * z) * (Real.cos (regularRationalAngle r p) : ℂ) +
        spectralT lam⁻¹ ((lam : ℂ) * z) := by
    rw [physical_spectralA_axis hlam.ne', physical_spectralS_axis, physical_spectralT_axis hlam.ne', add_comm]
    exact hinc
  have hdc : spectralDetF002 lam⁻¹ ((lam : ℂ) * z) ≠ 0 := by
    rw [axis_swap_determinant hlam.ne']
    exact neg_ne_zero.mpr hdet
  exact (positive_canonical_both_parities_all_det (inv_pos.mpr hlam) hzr.2.1 hr hrp hcop hp hc hdc
    (isOpen_omegaHF002 (inv_pos.mpr hlam)) (omegaHF002_subset_complement (inv_pos.mpr hlam))
    (fun w hw => (endpoint_boundary_criterion (inv_pos.mpr hlam)).1
      (frontier_omegaHF002_subset_endpoint (inv_pos.mpr hlam) hw)) hzr.1
    (physical_high_domain_conj lam⁻¹)).1

theorem regular_second_low_rational_obstruction {lam e : ℝ} {z : ℂ} {r p : ℕ}
    (hlam : 0 < lam) (hz : z ∈ regularBoundaryF002 lam (omegaL lam))
    (hr : 0 < r) (hrp : 2 * r < p) (hcop : r.Coprime p) (hp : Odd p)
    (he : e = 1 ∨ e = -1)
    (hinc : spectralA lam z = spectralS z * (e : ℂ) +
      spectralT lam z * (Real.cos (regularRationalAngle r p) : ℂ))
    (hdet : spectralDetF002 lam z ≠ 0) :
    ¬ HasDomainExtension (omegaL lam) (lowNormalizedBulk lam) z := by
  apply original_low_nonextension_of_axis_canonical hlam hz
  have hzr := physical_regularBoundary_axis hlam (physical_low_domain_axis hlam) hz
  have hc : spectralA lam⁻¹ ((lam : ℂ) * z) =
      spectralS ((lam : ℂ) * z) * (Real.cos (regularRationalAngle r p) : ℂ) +
        spectralT lam⁻¹ ((lam : ℂ) * z) * (e : ℂ) := by
    rw [physical_spectralA_axis hlam.ne', physical_spectralS_axis, physical_spectralT_axis hlam.ne', add_comm]
    exact hinc
  have hdc : spectralDetF002 lam⁻¹ ((lam : ℂ) * z) ≠ 0 := by
    rw [axis_swap_determinant hlam.ne']
    exact neg_ne_zero.mpr hdet
  have hf : frontier (omegaL lam⁻¹) ⊆ spectralSetF002 lam⁻¹ :=
    fun w hw => (endpoint_boundary_criterion (inv_pos.mpr hlam)).1
      (frontier_omegaLF002_subset_endpoint (inv_pos.mpr hlam) hw)
  rcases he with rfl | rfl
  · exact (positive_canonical_both_parities_all_det (inv_pos.mpr hlam) hzr.2.1 hr hrp hcop hp
      (by simpa using hc) hdc (isOpen_omegaLF002 (inv_pos.mpr hlam))
      (omegaLF002_subset_complement (inv_pos.mpr hlam)) hf hzr.1 (physical_low_domain_conj lam⁻¹)).2
  · exact negativeLT_canonical_even_all_det (inv_pos.mpr hlam) hzr.2.1 hr hrp hcop hp
      (by simpa [sub_eq_add_neg] using hc) hdc (isOpen_omegaLF002 (inv_pos.mpr hlam))
      (omegaLF002_subset_complement (inv_pos.mpr hlam)) hf hzr.1 (physical_low_domain_conj lam⁻¹)

end
end IsingBulk.AnisoF002.RegularTail.C03
