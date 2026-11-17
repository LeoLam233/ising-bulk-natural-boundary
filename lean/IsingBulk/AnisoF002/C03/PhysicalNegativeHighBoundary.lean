import IsingBulk.AnisoF002.C03.NegativePhysicalNoncancellation
import IsingBulk.AnisoF002.C03.NegativePhysicalSquareRoot
import IsingBulk.AnisoF002.C03.PhysicalNegativeObstruction
import IsingBulk.AnisoF002.C03.PhysicalPositiveHighBoundary

/-!
# Full original anisotropic high-temperature natural boundary

The complete physical negative-HT Taylor noncancellation supplies every
reduced odd rational obstruction. Conjugation handles both determinant
signs, actual boundary charts give density, and axis exchange handles
both spectral directions. Regular-boundary closure reaches every finite
frontier point of the exact original physical domain, including Re z=0.
The isotropic ratio remains the independent F002 isotropic mechanism.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open IsingBulk.Anisotropic IsingBulk.Anisotropic.FormFactors
  IsingBulk.AnisoF002.Geometry IsingBulk.AnisoF002.NegativeHT Set Filter
open scoped Topology BigOperators ComplexConjugate

theorem negative_high_canonical_rational_obstruction_neg_det {lam : ℝ} {z : ℂ} {a p : ℕ}
    (hlam : 0 < lam) (hz : z ∈ regularBoundaryF002 lam (omegaH lam))
    (ha : 0 < a) (hap : 2 * a < p) (hcop : a.Coprime p) (hp : Odd p)
    (hinc : spectralA lam z = spectralS z * (Real.cos (regularRationalAngle a p) : ℂ) +
      spectralT lam z * (-1)) (hdet : spectralDetF002 lam z < 0) :
    ¬ HasDomainExtension (omegaH lam) (canonicalAngularTailF002 lam 0) z := by
  have hφ := regularRationalAngle_mem ha hap
  obtain ⟨Z, B, hZa, hZ0, hBa, _, hBi, _, hside, hcor⟩ :=
    exists_negative_original_odd_chart hlam hz hφ.1 hφ.2 hinc hdet
  have hBn : B 0 ≠ 0 := Complex.slitPlane_ne_zero (Or.inr hBi.ne)
  have hsqrt : Complex.sqrt (B 0) ^ 2 = B 0 := by
    simpa only [Complex.sqrt] using Complex.cpow_ofNat_inv_pow (B 0) 2
  let b : ℂ → ℂ := normalizedLocalSquareRoot B (Complex.sqrt (B 0))
  have hba : AnalyticAt ℂ b 0 := normalizedLocalSquareRoot_analyticAt _ hBa hBn
  have hbsq : ∀ t, b t ^ 2 = B t := normalizedLocalSquareRoot_sq hBn hsqrt
  have hno := negative_physical_odd_sum_no_analytic_inward_germ hba hBa hφ.1 hφ.2
    hBi hbsq hp hcop (show regularRationalAngle a p = 2 * Real.pi * a / p from rfl)
  have hσsq := physical_root_branch_sign_sq hBn (hbsq 0)
  have hσ : Complex.sqrt (B 0) / b 0 ≠ 0 := by
    intro he
    simp only [he, zero_pow two_ne_zero, zero_ne_one] at hσsq
  exact no_extension_of_negative_inward_correspondence (isOpen_omegaHF002 hlam)
    hZa hZ0 hσ hside (hcor b hba hbsq) hno

theorem negative_high_canonical_rational_obstruction_all_det {lam : ℝ} {z : ℂ} {a p : ℕ}
    (hlam : 0 < lam) (hz : z ∈ regularBoundaryF002 lam (omegaH lam))
    (ha : 0 < a) (hap : 2 * a < p) (hcop : a.Coprime p) (hp : Odd p)
    (hinc : spectralA lam z = spectralS z * (Real.cos (regularRationalAngle a p) : ℂ) +
      spectralT lam z * (-1)) (hdet : spectralDetF002 lam z ≠ 0) :
    ¬ HasDomainExtension (omegaH lam) (canonicalAngularTailF002 lam 0) z := by
  by_cases hd : spectralDetF002 lam z < 0
  · exact negative_high_canonical_rational_obstruction_neg_det hlam hz ha hap hcop hp hinc hd
  have hdpos : 0 < spectralDetF002 lam z := lt_of_le_of_ne (le_of_not_gt hd) hdet.symm
  have hc : spectralA lam (conj z) =
      spectralS (conj z) * (Real.cos (regularRationalAngle a p) : ℂ) +
        spectralT lam (conj z) * (-1) := by
    simpa only [physical_spectralA_conj, physical_spectralS_conj, physical_spectralT_conj,
      map_add, map_mul, map_neg, map_one, Complex.conj_ofReal] using congrArg conj hinc
  have hdc : spectralDetF002 lam (conj z) < 0 := by
    rw [physical_spectralDet_conj]
    exact neg_neg_of_pos hdpos
  have hn := negative_high_canonical_rational_obstruction_neg_det hlam
    (physical_regularBoundary_conj (physical_high_domain_conj lam) hz) ha hap hcop hp hc hdc
  exact fun he => hn (physical_canonical_extension_conjugate (physical_high_domain_conj lam)
    (omegaHF002_subset_complement hlam) hz.2.1 hdet he)

theorem regular_first_negative_high_canonical_obstruction {lam : ℝ} {z : ℂ}
    (hlam : 0 < lam) (hz : z ∈ regularBoundaryF002 lam (omegaH lam)) (hx : z.re < 0)
    (hf : geometryF1 lam z.re z.im = 0) (hg : geometryF2 lam z.re z.im ≠ 0) :
    ¬ HasDomainExtension (omegaH lam) (canonicalAngularTailF002 lam 0) z := by
  have hfront : frontier (omegaH lam) ⊆ spectralSetF002 lam :=
    fun w hw => (endpoint_boundary_criterion hlam).1 (frontier_omegaHF002_subset_endpoint hlam hw)
  obtain ⟨b, e, ψ, hb, he, hψ, hψ0, hnear⟩ := exists_regular_first_boundary_parameters hlam hz
    (isOpen_omegaHF002 hlam) (omegaHF002_subset_complement hlam) hfront hf hg
  have hinc : spectralA lam z = spectralS z * (b : ℂ) + spectralT lam z * (e : ℂ) := by
    simpa only [hψ0] using hnear.self_of_nhds.2.2
  have he1 := physical_negative_high_endpoint_sign hlam hz.1 hx hb he hinc
  subst e
  have hfreq := (mem_closure_iff_frequently.mp (regularRationalCosines_closure hb)).and_eventually hnear
  have hno : ∃ᶠ u in 𝓝 b,
      ψ u ∈ {w | ¬ HasDomainExtension (omegaH lam) (canonicalAngularTailF002 lam 0) w} := by
    apply hfreq.mono
    rintro u ⟨⟨a, p, ha, hap, hcop, hp, hur⟩, hu⟩
    exact negative_high_canonical_rational_obstruction_all_det hlam hu.1 ha hap hcop hp
      (by simpa only [hur, Complex.ofReal_neg, Complex.ofReal_one] using hu.2.2) hu.2.1
  have hcl := mem_closure_of_frequently_of_tendsto hno hψ.tendsto
  rw [hψ0] at hcl
  exact nonextension_on_obstruction_closure (fun _ h => h) hcl

theorem regular_negative_high_normalized_obstruction {lam : ℝ} {z : ℂ}
    (hlam : 0 < lam) (hz : z ∈ regularBoundaryF002 lam (omegaH lam)) (hx : z.re < 0) :
    ¬ HasDomainExtension (omegaH lam) (highNormalizedBulk lam) z := by
  rcases regularBoundaryF002_factors hlam (frontier_omegaHF002_subset_endpoint hlam) hz with hf | hf
  · have hd := (regular_first_endpoint_exists_all_re hlam hz.2.1 hf.1 hf.2).1
    exact original_high_nonextension_of_canonical hlam hz hd
      (regular_first_negative_high_canonical_obstruction hlam hz hx hf.1 hf.2)
  · have hzr := physical_regularBoundary_axis hlam (physical_high_domain_axis hlam) hz
    have hx' : ((lam : ℂ) * z).re < 0 := by
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
        mul_neg_of_pos_of_neg hlam hx
    have hf' : geometryF1 lam⁻¹ ((lam : ℂ) * z).re ((lam : ℂ) * z).im = 0 := by
      rw [axis_swap_first_factor hlam.ne']
      exact hf.1
    have hg' : geometryF2 lam⁻¹ ((lam : ℂ) * z).re ((lam : ℂ) * z).im ≠ 0 := by
      rw [axis_swap_second_factor hlam.ne']
      exact hf.2
    have hd := (regular_first_endpoint_exists_all_re (inv_pos.mpr hlam) hzr.2.1 hf' hg').1
    rw [axis_swap_determinant hlam.ne', neg_ne_zero] at hd
    exact original_high_nonextension_of_axis_canonical hlam hz hd
      (regular_first_negative_high_canonical_obstruction (inv_pos.mpr hlam) hzr hx' hf' hg')

theorem regular_high_normalized_obstruction {lam : ℝ} {z : ℂ}
    (hlam : 0 < lam) (hz : z ∈ regularBoundaryF002 lam (omegaH lam)) :
    ¬ HasDomainExtension (omegaH lam) (highNormalizedBulk lam) z := by
  rcases lt_or_gt_of_ne hz.2.1 with hx | hx
  · exact regular_negative_high_normalized_obstruction hlam hz hx
  · exact regular_positive_high_normalized_obstruction hlam hz hx

theorem anisotropic_high_normalized_naturalBoundary {lam : ℝ}
    (hlam : 0 < lam) (hne : lam ≠ 1) : NaturalBoundaryOn (omegaH lam) (highNormalizedBulk lam) :=
  literal_high_boundary_of_regular_obstructions hlam hne
    (literal_highNormalizedBulk_analyticOnNhd hlam) (fun _ hz => regular_high_normalized_obstruction hlam hz)

theorem anisotropic_high_physical_naturalBoundary {J lam : ℝ}
    (hJ : 0 < J) (hlam : 0 < lam) (hne : lam ≠ 1) :
    NaturalBoundaryOn (omegaH lam) (highPhysicalBulk J lam) :=
  literal_high_energy_boundary hJ hlam (anisotropic_high_normalized_naturalBoundary hlam hne)

end
end IsingBulk.AnisoF002.RegularTail.C03
