import IsingBulk.AnisoF002.C03.IsotropicRadialBoundary
import IsingBulk.AnisoF002.C03.PhysicalGlobalHolomorphy
import IsingBulk.AnisoF002.C03.GlobalTransfer
import IsingBulk.Anisotropic.Final.Target

/-!
# Full original isotropic natural-boundary transfer

The chosen physical fourth roots have genuine local nonzero extensions
at every noncritical point. The actual canonical obstruction therefore
transfers to the exact original normalized susceptibility. Closure restores
all finite frontier points, including both HT tips and every LT contact.
The physical energy normalization is the unchanged z/(2J).
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology
open Set Filter IsingBulk.Anisotropic IsingBulk.Anisotropic.FormFactors
open IsingBulk.AnisoF002.Geometry IsingBulk.AnisoF002.RegularTail.C03

theorem complex_fourth_power_ne_one_of_nonzero_parts {s : ℂ}
    (hr : s.re ≠ 0) (hi : s.im ≠ 0) : s ^ 4 ≠ 1 := by
  intro he
  have hh : (s ^ 2) ^ 2 = 1 := by simpa only [← pow_mul] using he
  rcases sq_eq_one_iff.mp hh with hp | hm
  · rcases sq_eq_one_iff.mp hp with he | he
    · exact hi (by rw [he, Complex.one_im])
    · exact hi (by rw [he]; norm_num)
  · have hI : (s * Complex.I) ^ 2 = 1 := by rw [mul_pow, hm, Complex.I_sq]; norm_num
    rcases sq_eq_one_iff.mp hI with he | he
    · apply hr
      simpa only [Complex.mul_im, Complex.I_re, Complex.I_im, mul_one, mul_zero,
        add_zero, Complex.one_im] using congrArg Complex.im he
    · apply hr
      simpa only [Complex.mul_im, Complex.I_re, Complex.I_im, mul_one, mul_zero,
        add_zero, Complex.neg_im, Complex.one_im, neg_zero] using congrArg Complex.im he

theorem isotropic_spectralProduct_sq (z : ℂ) :
    spectralProduct 1 z ^ 2 = Complex.sinh z ^ 4 := by
  change (spectralS z * spectralT 1 z) ^ 2 = _
  rw [isotropic_spectralT]
  change (Complex.sinh z * Complex.sinh z) ^ 2 = _
  ring

theorem isotropic_original_high_nonextension {z : ℂ}
    (hz : z ∈ isotropicNoncriticalBoundary (omegaH 1))
    (hno : ¬ HasDomainExtension (omegaH 1) (canonicalAngularTailF002 1 0) z) :
    ¬ HasDomainExtension (omegaH 1) (highNormalizedBulk 1) z := by
  intro he
  have hx := sinh_real_ne_zero_implies_re_ne_zero hz.2.1
  have hS := spectralS_ne_zero_of_re_ne_zero hx
  have hB : spectralRatioF002 1 z ∈ Complex.slitPlane := by
    rw [spectralRatioF002, isotropic_spectralT, div_self hS]
    exact Or.inl (by norm_num)
  have hmul := extension_mul_local_analytic (canonicalTransferFactor_analyticAt hS hB) he
  have hraw : HasDomainExtension (omegaH 1) (highPrefactor 1 * canonicalAngularTailF002 1 0) z := by
    apply extension_of_local_domain_equality (Eventually.of_forall (fun w hw => ?_)) hmul
    exact (original_high_normalized_canonical_identity (by norm_num) hw).symm
  have hp1 : spectralProduct 1 z ^ 2 ≠ 1 := by
    rw [isotropic_spectralProduct_sq]
    exact complex_fourth_power_ne_one_of_nonzero_parts hz.2.1 hz.2.2
  obtain ⟨g, hg, hg0, hge⟩ := Physical.highPrefactor_local_nonzero_extension
    (by norm_num : (0 : ℝ) < 1) hz.1 hx hp1
  exact hno (Physical.extension_cancel_locally_extended_factor hg hg0 hge hraw)

theorem isotropic_original_low_nonextension {z : ℂ}
    (hz : z ∈ isotropicNoncriticalBoundary (omegaL 1))
    (hno : ¬ HasDomainExtension (omegaL 1) (canonicalAngularTailF002 1 1) z) :
    ¬ HasDomainExtension (omegaL 1) (lowNormalizedBulk 1) z := by
  intro he
  have hS := spectralS_ne_zero_of_re_ne_zero (sinh_real_ne_zero_implies_re_ne_zero hz.2.1)
  have hp0 : spectralProduct 1 z ≠ 0 := by
    change spectralS z * spectralT 1 z ≠ 0
    rw [isotropic_spectralT]
    exact mul_ne_zero hS hS
  have hp1 : spectralProduct 1 z ^ 2 ≠ 1 := by
    rw [isotropic_spectralProduct_sq]
    exact complex_fourth_power_ne_one_of_nonzero_parts hz.2.1 hz.2.2
  have hraw : HasDomainExtension (omegaL 1) (lowPrefactor 1 * canonicalAngularTailF002 1 1) z := by
    apply extension_of_local_domain_equality (Eventually.of_forall (fun w hw => ?_)) he
    exact (original_low_normalized_canonical_identity (by norm_num) hw).symm
  obtain ⟨g, hg, hg0, hge⟩ := Physical.lowPrefactor_local_nonzero_extension
    (by norm_num : (0 : ℝ) < 1) hz.1 hp0 hp1
  exact hno (Physical.extension_cancel_locally_extended_factor hg hg0 hge hraw)

theorem isotropic_high_normalized_boundary_of_dense_radial {A : Set ℝ}
    (hA : A ⊆ Ioo (0 : ℝ) Real.pi)
    (hd : ∀ α ∈ Ioo (0 : ℝ) Real.pi, α ≠ Real.pi / 2 → α ∈ closure A)
    (hno : ∀ α ∈ A, ¬ HasIsotropicRadialGerm (isotropicFullParticleSeries 0 0 1) α) :
    NaturalBoundaryOn (omegaH 1) (highNormalizedBulk 1) := by
  apply natural_boundary_of_obstruction_closure
    (literal_highNormalizedBulk_analyticOnNhd (by norm_num : (0 : ℝ) < 1))
    (S := isotropicNoncriticalBoundary (omegaH 1))
  · rw [isotropic_high_noncritical_dense]
  · intro z hz
    exact isotropic_original_high_nonextension hz
      (isotropic_high_all_noncritical_noextension 0 hA hd hno hz)

theorem isotropic_low_normalized_boundary_of_dense_radial {A : Set ℝ}
    (hA : A ⊆ Ioo (0 : ℝ) Real.pi)
    (hd : ∀ α ∈ Ioo (0 : ℝ) Real.pi, α ≠ Real.pi / 2 → α ∈ closure A)
    (hno : ∀ α ∈ A, ¬ HasIsotropicRadialGerm (isotropicFullParticleSeries 1 0 1) α) :
    NaturalBoundaryOn (omegaL 1) (lowNormalizedBulk 1) := by
  apply natural_boundary_of_obstruction_closure
    (literal_lowNormalizedBulk_analyticOnNhd (by norm_num : (0 : ℝ) < 1))
    (S := isotropicNoncriticalBoundary (omegaL 1))
  · rw [isotropic_low_noncritical_dense]
  · intro z hz
    exact isotropic_original_low_nonextension hz
      (isotropic_low_all_noncritical_noextension 1 hA hd hno hz)

theorem isotropic_high_physical_boundary_of_dense_radial {A : Set ℝ} {J : ℝ}
    (hJ : 0 < J) (hA : A ⊆ Ioo (0 : ℝ) Real.pi)
    (hd : ∀ α ∈ Ioo (0 : ℝ) Real.pi, α ≠ Real.pi / 2 → α ∈ closure A)
    (hno : ∀ α ∈ A, ¬ HasIsotropicRadialGerm (isotropicFullParticleSeries 0 0 1) α) :
    NaturalBoundaryOn (omegaH 1) (highPhysicalBulk J 1) :=
  literal_high_energy_boundary hJ (by norm_num)
    (isotropic_high_normalized_boundary_of_dense_radial hA hd hno)

theorem isotropic_low_physical_boundary_of_dense_radial {A : Set ℝ} {J : ℝ}
    (hJ : 0 < J) (hA : A ⊆ Ioo (0 : ℝ) Real.pi)
    (hd : ∀ α ∈ Ioo (0 : ℝ) Real.pi, α ≠ Real.pi / 2 → α ∈ closure A)
    (hno : ∀ α ∈ A, ¬ HasIsotropicRadialGerm (isotropicFullParticleSeries 1 0 1) α) :
    NaturalBoundaryOn (omegaL 1) (lowPhysicalBulk J 1) :=
  literal_low_energy_boundary hJ (by norm_num)
    (isotropic_low_normalized_boundary_of_dense_radial hA hd hno)

end IsingBulk.AnisoF002.Isotropic
