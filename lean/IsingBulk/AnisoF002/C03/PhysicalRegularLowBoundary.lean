import IsingBulk.AnisoF002.C03.PhysicalAxisObstruction
import IsingBulk.AnisoF002.C03.PhysicalBoundaryParameters
import IsingBulk.AnisoF002.C03.RegularRationalDensity
import IsingBulk.AnisoF002.C03.GlobalTransfer
import IsingBulk.Anisotropic.Final.Target

/-!
# The original anisotropic low-temperature natural boundary

Rational first singularities are dense on every actual regular boundary
arc.  Both endpoint signs and both lattice directions are included.
The previously proved density of regular points then reaches every
finite frontier point of the exact original low-temperature domain.
The isotropic value remains the separate F002 isotropic mechanism.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open IsingBulk.Anisotropic IsingBulk.Anisotropic.FormFactors IsingBulk.AnisoF002.Geometry
  Set Filter
open scoped Topology

theorem regular_first_low_canonical_rational_obstruction {lam e : ℝ} {z : ℂ} {r p : ℕ}
    (hlam : 0 < lam) (hz : z ∈ regularBoundaryF002 lam (omegaL lam))
    (hr : 0 < r) (hrp : 2 * r < p) (hcop : r.Coprime p) (hp : Odd p)
    (he : e = 1 ∨ e = -1)
    (hinc : spectralA lam z = spectralS z * (Real.cos (regularRationalAngle r p) : ℂ) +
      spectralT lam z * (e : ℂ)) (hdet : spectralDetF002 lam z ≠ 0) :
    ¬ HasDomainExtension (omegaL lam) (canonicalAngularTailF002 lam 1) z := by
  have hf : frontier (omegaL lam) ⊆ spectralSetF002 lam :=
    fun w hw => (endpoint_boundary_criterion hlam).1 (frontier_omegaLF002_subset_endpoint hlam hw)
  rcases he with rfl | rfl
  · exact (positive_canonical_both_parities_all_det hlam hz.2.1 hr hrp hcop hp (by simpa using hinc) hdet
      (isOpen_omegaLF002 hlam) (omegaLF002_subset_complement hlam) hf hz.1
      (physical_low_domain_conj lam)).2
  · exact negativeLT_canonical_even_all_det hlam hz.2.1 hr hrp hcop hp
      (by simpa [sub_eq_add_neg] using hinc) hdet
      (isOpen_omegaLF002 hlam) (omegaLF002_subset_complement hlam) hf hz.1
      (physical_low_domain_conj lam)

theorem regular_first_low_canonical_obstruction {lam : ℝ} {z : ℂ}
    (hlam : 0 < lam) (hz : z ∈ regularBoundaryF002 lam (omegaL lam))
    (hf : geometryF1 lam z.re z.im = 0) (hg : geometryF2 lam z.re z.im ≠ 0) :
    ¬ HasDomainExtension (omegaL lam) (canonicalAngularTailF002 lam 1) z := by
  obtain ⟨b, e, ψ, hb, he, hψ, hψ0, hnear⟩ := exists_regular_first_boundary_parameters hlam hz
    (isOpen_omegaLF002 hlam) (omegaLF002_subset_complement hlam)
    (fun w hw => (endpoint_boundary_criterion hlam).1 (frontier_omegaLF002_subset_endpoint hlam hw)) hf hg
  have hfreq := (mem_closure_iff_frequently.mp (regularRationalCosines_closure hb)).and_eventually hnear
  have hno : ∃ᶠ u in 𝓝 b, ψ u ∈ {w | ¬ HasDomainExtension (omegaL lam) (canonicalAngularTailF002 lam 1) w} := by
    apply hfreq.mono
    rintro u ⟨⟨r, p, hr, hrp, hcop, hp, hur⟩, hu⟩
    exact regular_first_low_canonical_rational_obstruction hlam hu.1 hr hrp hcop hp he
      (by simpa only [hur] using hu.2.2) hu.2.1
  have hcl := mem_closure_of_frequently_of_tendsto hno hψ.tendsto
  rw [hψ0] at hcl
  exact nonextension_on_obstruction_closure (fun _ h => h) hcl

theorem regular_low_normalized_obstruction {lam : ℝ} {z : ℂ}
    (hlam : 0 < lam) (hz : z ∈ regularBoundaryF002 lam (omegaL lam)) :
    ¬ HasDomainExtension (omegaL lam) (lowNormalizedBulk lam) z := by
  rcases regularBoundaryF002_factors hlam (frontier_omegaLF002_subset_endpoint hlam) hz with hf | hf
  · exact original_low_nonextension_of_canonical hlam hz
      (regular_first_low_canonical_obstruction hlam hz hf.1 hf.2)
  · apply original_low_nonextension_of_axis_canonical hlam hz
    have hzr := physical_regularBoundary_axis hlam (physical_low_domain_axis hlam) hz
    apply regular_first_low_canonical_obstruction (inv_pos.mpr hlam) hzr
    · rw [axis_swap_first_factor hlam.ne']
      exact hf.1
    · rw [axis_swap_second_factor hlam.ne']
      exact hf.2

theorem anisotropic_low_normalized_naturalBoundary {lam : ℝ}
    (hlam : 0 < lam) (hne : lam ≠ 1) : NaturalBoundaryOn (omegaL lam) (lowNormalizedBulk lam) :=
  literal_low_boundary_of_regular_obstructions hlam hne
    (literal_lowNormalizedBulk_analyticOnNhd hlam) (fun _ hz => regular_low_normalized_obstruction hlam hz)

theorem anisotropic_low_physical_naturalBoundary {J lam : ℝ}
    (hJ : 0 < J) (hlam : 0 < lam) (hne : lam ≠ 1) :
    NaturalBoundaryOn (omegaL lam) (lowPhysicalBulk J lam) :=
  literal_low_energy_boundary hJ hlam (anisotropic_low_normalized_naturalBoundary hlam hne)

end
end IsingBulk.AnisoF002.RegularTail.C03
