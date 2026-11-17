import IsingBulk.AnisoF002.C03.PhysicalRegularLowBoundary

/-!
# The complete original high-temperature obstruction on positive real part

The actual HT strip fixes the endpoint sign to +1 when Re z > 0.
Both spectral directions, determinant signs and all lower/larger odd
particle competitors are covered before taking the boundary closure.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open IsingBulk.Anisotropic IsingBulk.Anisotropic.FormFactors IsingBulk.AnisoF002.Geometry
  Set Filter
open scoped Topology

theorem physical_high_boundary_cos_nonneg {lam : ℝ} {z : ℂ}
    (hlam : 0 < lam) (hz : z ∈ frontier (omegaH lam)) : 0 ≤ Real.cos z.im := by
  have hy : |z.im| ≤ highStripWidthF002 lam := by
    change z ∈ frontier (omegaHF002 lam) at hz
    rw [frontier_omegaHF002 hlam] at hz
    exact hz.1
  have hw : highStripWidthF002 lam ≤ Real.pi / 2 := by
    unfold highStripWidthF002
    apply div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num : (0 : ℝ) < 2)
    nlinarith [le_max_left (1 : ℝ) lam]
  exact Real.cos_nonneg_of_mem_Icc (abs_le.mp (hy.trans hw))

theorem physical_positive_high_endpoint_sign {lam b e : ℝ} {z : ℂ}
    (hlam : 0 < lam) (hz : z ∈ frontier (omegaH lam)) (hx : 0 < z.re)
    (hb : |b| < 1) (he : e = 1 ∨ e = -1)
    (hinc : spectralA lam z = spectralS z * (b : ℂ) + spectralT lam z * (e : ℂ)) : e = 1 := by
  have hs := first_endpoint_signed_equation
    (show b ∈ Icc (-1 : ℝ) 1 from ⟨(abs_lt.mp hb).1.le, (abs_lt.mp hb).2.le⟩) he hinc
  have hpos := mul_pos (Real.cosh_pos z.re) (Real.sinh_pos_iff.mpr (mul_pos hlam hx))
  have hnonneg := mul_nonneg (Real.cosh_pos (lam * z.re)).le (physical_high_boundary_cos_nonneg hlam hz)
  rcases he with he | rfl
  · exact he
  · norm_num at hs
    nlinarith

theorem physical_negative_high_endpoint_sign {lam b e : ℝ} {z : ℂ}
    (hlam : 0 < lam) (hz : z ∈ frontier (omegaH lam)) (hx : z.re < 0)
    (hb : |b| < 1) (he : e = 1 ∨ e = -1)
    (hinc : spectralA lam z = spectralS z * (b : ℂ) + spectralT lam z * (e : ℂ)) : e = -1 := by
  have hs := first_endpoint_signed_equation
    (show b ∈ Icc (-1 : ℝ) 1 from ⟨(abs_lt.mp hb).1.le, (abs_lt.mp hb).2.le⟩) he hinc
  have hneg := mul_neg_of_pos_of_neg (Real.cosh_pos z.re)
    (Real.sinh_neg_iff.mpr (mul_neg_of_pos_of_neg hlam hx))
  have hnonneg := mul_nonneg (Real.cosh_pos (lam * z.re)).le (physical_high_boundary_cos_nonneg hlam hz)
  rcases he with rfl | he
  · norm_num at hs
    linarith
  · exact he

theorem regular_first_positive_high_canonical_obstruction {lam : ℝ} {z : ℂ}
    (hlam : 0 < lam) (hz : z ∈ regularBoundaryF002 lam (omegaH lam)) (hx : 0 < z.re)
    (hf : geometryF1 lam z.re z.im = 0) (hg : geometryF2 lam z.re z.im ≠ 0) :
    ¬ HasDomainExtension (omegaH lam) (canonicalAngularTailF002 lam 0) z := by
  have hfront : frontier (omegaH lam) ⊆ spectralSetF002 lam :=
    fun w hw => (endpoint_boundary_criterion hlam).1 (frontier_omegaHF002_subset_endpoint hlam hw)
  obtain ⟨b, e, ψ, hb, he, hψ, hψ0, hnear⟩ := exists_regular_first_boundary_parameters hlam hz
    (isOpen_omegaHF002 hlam) (omegaHF002_subset_complement hlam) hfront hf hg
  have hinc : spectralA lam z = spectralS z * (b : ℂ) + spectralT lam z * (e : ℂ) := by
    simpa only [hψ0] using hnear.self_of_nhds.2.2
  have he1 := physical_positive_high_endpoint_sign hlam hz.1 hx hb he hinc
  subst e
  have hfreq := (mem_closure_iff_frequently.mp (regularRationalCosines_closure hb)).and_eventually hnear
  have hno : ∃ᶠ u in 𝓝 b, ψ u ∈ {w | ¬ HasDomainExtension (omegaH lam) (canonicalAngularTailF002 lam 0) w} := by
    apply hfreq.mono
    rintro u ⟨⟨r, p, hr, hrp, hcop, hp, hur⟩, hu⟩
    exact (positive_canonical_both_parities_all_det hlam hu.1.2.1 hr hrp hcop hp
      (by simpa only [hur, Complex.ofReal_one, mul_one] using hu.2.2) hu.2.1
      (isOpen_omegaHF002 hlam) (omegaHF002_subset_complement hlam) hfront hu.1.1
      (physical_high_domain_conj lam)).1
  have hcl := mem_closure_of_frequently_of_tendsto hno hψ.tendsto
  rw [hψ0] at hcl
  exact nonextension_on_obstruction_closure (fun _ h => h) hcl

theorem regular_positive_high_normalized_obstruction {lam : ℝ} {z : ℂ}
    (hlam : 0 < lam) (hz : z ∈ regularBoundaryF002 lam (omegaH lam)) (hx : 0 < z.re) :
    ¬ HasDomainExtension (omegaH lam) (highNormalizedBulk lam) z := by
  rcases regularBoundaryF002_factors hlam (frontier_omegaHF002_subset_endpoint hlam) hz with hf | hf
  · have hd := (regular_first_endpoint_exists_all_re hlam hz.2.1 hf.1 hf.2).1
    exact original_high_nonextension_of_canonical hlam hz hd
      (regular_first_positive_high_canonical_obstruction hlam hz hx hf.1 hf.2)
  · have hzr := physical_regularBoundary_axis hlam (physical_high_domain_axis hlam) hz
    have hx' : 0 < ((lam : ℂ) * z).re := by
      simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using mul_pos hlam hx
    have hf' : geometryF1 lam⁻¹ ((lam : ℂ) * z).re ((lam : ℂ) * z).im = 0 := by
      rw [axis_swap_first_factor hlam.ne']
      exact hf.1
    have hg' : geometryF2 lam⁻¹ ((lam : ℂ) * z).re ((lam : ℂ) * z).im ≠ 0 := by
      rw [axis_swap_second_factor hlam.ne']
      exact hf.2
    have hd := (regular_first_endpoint_exists_all_re (inv_pos.mpr hlam) hzr.2.1 hf' hg').1
    rw [axis_swap_determinant hlam.ne', neg_ne_zero] at hd
    exact original_high_nonextension_of_axis_canonical hlam hz hd
      (regular_first_positive_high_canonical_obstruction (inv_pos.mpr hlam) hzr hx' hf' hg')

theorem positive_high_frontier_obstruction {lam : ℝ} {z : ℂ}
    (hlam : 0 < lam) (hne : lam ≠ 1) (hz : z ∈ frontier (omegaH lam)) (hx : 0 < z.re) :
    ¬ HasDomainExtension (omegaH lam) (highNormalizedBulk lam) z := by
  have hc : z ∈ closure (regularBoundaryF002 lam (omegaH lam)) := by
    rwa [literal_high_regular_dense hlam hne]
  have hf := (mem_closure_iff_frequently.mp hc).and_eventually
    (Complex.continuous_re.continuousAt.eventually (Ioi_mem_nhds hx))
  have hn : ∃ᶠ w in 𝓝 z, w ∈ {u | ¬ HasDomainExtension (omegaH lam) (highNormalizedBulk lam) u} :=
    hf.mono (fun _ h => regular_positive_high_normalized_obstruction hlam h.1 h.2)
  exact nonextension_on_obstruction_closure (fun _ h => h) hn.mem_closure

end
end IsingBulk.AnisoF002.RegularTail.C03
