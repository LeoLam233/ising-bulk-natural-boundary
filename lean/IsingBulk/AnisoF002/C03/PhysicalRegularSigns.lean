import IsingBulk.AnisoF002.C03.PhysicalNegativeLTObstruction
import IsingBulk.AnisoF002.C03.PhysicalConjugation

/-! # Complete regular obstructions for both determinant signs -/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open IsingBulk.Anisotropic IsingBulk.Anisotropic.FormFactors IsingBulk.AnisoF002.Geometry Set
open scoped ComplexConjugate

theorem positive_canonical_both_parities_all_det {lam : ℝ} {z : ℂ} {r p : ℕ} {D : Set ℂ}
    (hlam : 0 < lam) (hx : z.re ≠ 0)
    (hr : 0 < r) (hrp : 2 * r < p) (hcop : r.Coprime p) (hp : Odd p)
    (hinc : spectralA lam z = spectralS z * (Real.cos (regularRationalAngle r p) : ℂ) + spectralT lam z)
    (hdet : spectralDetF002 lam z ≠ 0)
    (hD : IsOpen D) (hDC : D ⊆ (spectralSetF002 lam)ᶜ)
    (hfront : frontier D ⊆ spectralSetF002 lam) (hz : z ∈ frontier D)
    (hconj : ∀ w, conj w ∈ D ↔ w ∈ D) :
    (¬ HasDomainExtension D (canonicalAngularTailF002 lam 0) z) ∧
      (¬ HasDomainExtension D (canonicalAngularTailF002 lam 1) z) := by
  by_cases hd : 0 < spectralDetF002 lam z
  · exact positive_canonical_both_parities_no_extension hlam hx hr hrp hcop hp hinc hd hD hDC hfront hz
  have hdneg : spectralDetF002 lam z < 0 := lt_of_le_of_ne (le_of_not_gt hd) hdet
  have hc : spectralA lam (conj z) =
      spectralS (conj z) * (Real.cos (regularRationalAngle r p) : ℂ) + spectralT lam (conj z) := by
    simpa only [physical_spectralA_conj, physical_spectralS_conj, physical_spectralT_conj,
      map_add, map_mul, Complex.conj_ofReal] using congrArg conj hinc
  have hdc : 0 < spectralDetF002 lam (conj z) := by
    rw [physical_spectralDet_conj]
    exact neg_pos.mpr hdneg
  have hn := positive_canonical_both_parities_no_extension hlam
    (by simpa only [Complex.conj_re] using hx) hr hrp hcop hp hc hdc hD hDC hfront
    ((physical_frontier_conj hconj z).mpr hz)
  exact ⟨fun he => hn.1 (physical_canonical_extension_conjugate hconj hDC hx hdet he),
    fun he => hn.2 (physical_canonical_extension_conjugate hconj hDC hx hdet he)⟩

theorem negativeLT_canonical_even_all_det {lam : ℝ} {z : ℂ} {r p : ℕ} {D : Set ℂ}
    (hlam : 0 < lam) (hx : z.re ≠ 0)
    (hr : 0 < r) (hrp : 2 * r < p) (hcop : r.Coprime p) (hp : Odd p)
    (hinc : spectralA lam z = spectralS z * (Real.cos (regularRationalAngle r p) : ℂ) - spectralT lam z)
    (hdet : spectralDetF002 lam z ≠ 0)
    (hD : IsOpen D) (hDC : D ⊆ (spectralSetF002 lam)ᶜ)
    (hfront : frontier D ⊆ spectralSetF002 lam) (hz : z ∈ frontier D)
    (hconj : ∀ w, conj w ∈ D ↔ w ∈ D) :
    ¬ HasDomainExtension D (canonicalAngularTailF002 lam 1) z := by
  by_cases hd : spectralDetF002 lam z < 0
  · exact negativeLT_canonical_even_no_extension hlam hx hr hrp hcop hp hinc hd hD hDC hfront hz
  have hdpos : 0 < spectralDetF002 lam z := lt_of_le_of_ne (le_of_not_gt hd) hdet.symm
  have hc : spectralA lam (conj z) =
      spectralS (conj z) * (Real.cos (regularRationalAngle r p) : ℂ) - spectralT lam (conj z) := by
    simpa only [physical_spectralA_conj, physical_spectralS_conj, physical_spectralT_conj,
      map_sub, map_mul, Complex.conj_ofReal] using congrArg conj hinc
  have hdc : spectralDetF002 lam (conj z) < 0 := by
    rw [physical_spectralDet_conj]
    exact neg_neg_of_pos hdpos
  have hn := negativeLT_canonical_even_no_extension hlam
    (by simpa only [Complex.conj_re] using hx) hr hrp hcop hp hc hdc hD hDC hfront
    ((physical_frontier_conj hconj z).mpr hz)
  exact fun he => hn (physical_canonical_extension_conjugate hconj hDC hx hdet he)

theorem positive_regular_high_obstruction_all_det {lam : ℝ} {z : ℂ} {r p : ℕ}
    (hlam : 0 < lam) (hz : z ∈ regularBoundaryF002 lam (omegaH lam))
    (hr : 0 < r) (hrp : 2 * r < p) (hcop : r.Coprime p) (hp : Odd p)
    (hinc : spectralA lam z = spectralS z * (Real.cos (regularRationalAngle r p) : ℂ) + spectralT lam z)
    (hdet : spectralDetF002 lam z ≠ 0) :
    ¬ HasDomainExtension (omegaH lam) (highNormalizedBulk lam) z := by
  apply original_high_nonextension_of_canonical hlam hz hdet
  exact (positive_canonical_both_parities_all_det hlam hz.2.1 hr hrp hcop hp hinc hdet
    (isOpen_omegaHF002 hlam) (omegaHF002_subset_complement hlam)
    (fun w hw => (endpoint_boundary_criterion hlam).1 (frontier_omegaHF002_subset_endpoint hlam hw)) hz.1
    (physical_high_domain_conj lam)).1

theorem regular_first_low_rational_obstruction {lam e : ℝ} {z : ℂ} {r p : ℕ}
    (hlam : 0 < lam) (hz : z ∈ regularBoundaryF002 lam (omegaL lam))
    (hr : 0 < r) (hrp : 2 * r < p) (hcop : r.Coprime p) (hp : Odd p)
    (he : e = 1 ∨ e = -1)
    (hinc : spectralA lam z = spectralS z * (Real.cos (regularRationalAngle r p) : ℂ) +
      spectralT lam z * (e : ℂ)) (hdet : spectralDetF002 lam z ≠ 0) :
    ¬ HasDomainExtension (omegaL lam) (lowNormalizedBulk lam) z := by
  apply original_low_nonextension_of_canonical hlam hz
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

end
end IsingBulk.AnisoF002.RegularTail.C03
