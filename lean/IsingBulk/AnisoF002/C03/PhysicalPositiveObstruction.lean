import IsingBulk.AnisoF002.C03.PhysicalSeriesAttachment
import IsingBulk.AnisoF002.C03.PhysicalInwardComponent
import IsingBulk.AnisoF002.C03.PhysicalRegularObstruction
import IsingBulk.AnisoF002.C03.RegularEvenFirstObstruction

/-!
# Original full physical susceptibilities at rational positive endpoints

The spectral inverse, its physical-domain side, both full parity tails,
their nonzero first singularities and the original contour/prefactor
identities are all attached.  There is no remaining inward membership,
coefficient identity or analytic-normalization premise in the physical
obstructions below.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set Filter IsingBulk.Anisotropic IsingBulk.Anisotropic.FormFactors IsingBulk.AnisoF002.Geometry
open scoped Topology

theorem no_extension_of_corresponding_inward_germs {D : Set ℂ} {F Z H : ℂ → ℂ} {z : ℂ}
    (hD : IsOpen D) (hZ : AnalyticAt ℂ Z 0) (hZ0 : Z 0 = z)
    (hside : ∀ᶠ eps : ℝ in 𝓝[>] (0 : ℝ), Z ((eps : ℂ) * Complex.I) ∈ D)
    (hcor : ∀ᶠ eps : ℝ in 𝓝[>] (0 : ℝ), H =ᶠ[𝓝 ((eps : ℂ) * Complex.I)] fun u => F (Z u))
    (hno : ¬ ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧
      ∀ᶠ eps : ℝ in 𝓝[>] (0 : ℝ), H =ᶠ[𝓝 ((eps : ℂ) * Complex.I)] g) :
    ¬ HasDomainExtension D F z := by
  apply no_extension_of_inward_chart hD hZ hZ0 hside
  rintro ⟨g, hg, he⟩
  apply hno
  refine ⟨g, hg, ?_⟩
  filter_upwards [hcor, he] with eps hc heps
  exact hc.trans heps

theorem positive_canonical_both_parities_no_extension {lam : ℝ} {z : ℂ} {r p : ℕ} {D : Set ℂ}
    (hlam : 0 < lam) (hx : z.re ≠ 0)
    (hr : 0 < r) (hrp : 2 * r < p) (hcop : r.Coprime p) (hp : Odd p)
    (hinc : spectralA lam z = spectralS z * (Real.cos (regularRationalAngle r p) : ℂ) + spectralT lam z)
    (hdet : 0 < spectralDetF002 lam z)
    (hD : IsOpen D) (hDC : D ⊆ (spectralSetF002 lam)ᶜ)
    (hfront : frontier D ⊆ spectralSetF002 lam) (hz : z ∈ frontier D) :
    (¬ HasDomainExtension D (canonicalAngularTailF002 lam 0) z) ∧
      (¬ HasDomainExtension D (canonicalAngularTailF002 lam 1) z) := by
  have hb := regularRational_cos_abs_lt_one hr hrp
  obtain ⟨Z, B, d, hZa, hZ0, _, _, hB0, hB, hchart, hleft⟩ :=
    exists_positive_physical_edge_control hlam hx hb hinc hdet
  have hBi : 0 < (B 0).im := by
    rw [hB0]
    change 0 < (spectralRatioF002 lam z).im
    rw [spectralRatioF002_im]
    exact div_pos hdet (Complex.normSq_pos.mpr (spectralS_ne_zero_of_re_ne_zero hx))
  have hside := positive_physical_chart_inward_domain hx hb hinc hdet hD hDC hfront hz
    hZa hZ0 (hchart.mono fun _ h => h.1) hleft
  obtain ⟨eps1, heps1, _, hcanon⟩ := exists_canonical_regular_germs d hB
    (hchart.mono fun _ h => h.2)
  have hcor (m : ℕ) : ∀ᶠ eps : ℝ in 𝓝[>] (0 : ℝ),
      edgeParticleTail (affineEdgeCenter (Real.cos (regularRationalAngle r p))) B m
        =ᶠ[𝓝 ((eps : ℂ) * Complex.I)] fun u => canonicalAngularTailF002 lam m (Z u) := by
    filter_upwards [self_mem_nhdsWithin,
      (gt_mem_nhds heps1).filter_mono nhdsWithin_le_nhds] with eps he he1
    exact (hcanon eps he he1.le).mono fun _ h => h.2 m
  exact ⟨no_extension_of_corresponding_inward_germs hD hZa hZ0 hside (hcor 0)
      (d.rational_odd_series_no_analytic_inward_germ hr hrp hcop hp hBi),
    no_extension_of_corresponding_inward_germs hD hZa hZ0 hside (hcor 1)
      (d.rational_even_series_no_analytic_inward_germ hr hrp hcop hp hBi)⟩

theorem positive_regular_high_normalized_obstruction {lam : ℝ} {z : ℂ} {r p : ℕ}
    (hlam : 0 < lam) (hz : z ∈ regularBoundaryF002 lam (omegaH lam))
    (hr : 0 < r) (hrp : 2 * r < p) (hcop : r.Coprime p) (hp : Odd p)
    (hinc : spectralA lam z = spectralS z * (Real.cos (regularRationalAngle r p) : ℂ) + spectralT lam z)
    (hdet : 0 < spectralDetF002 lam z) :
    ¬ HasDomainExtension (omegaH lam) (highNormalizedBulk lam) z := by
  apply original_high_nonextension_of_canonical hlam hz hdet.ne'
  exact (positive_canonical_both_parities_no_extension hlam hz.2.1 hr hrp hcop hp hinc hdet
    (isOpen_omegaHF002 hlam) (omegaHF002_subset_complement hlam)
    (fun w hw => (endpoint_boundary_criterion hlam).1 (frontier_omegaHF002_subset_endpoint hlam hw)) hz.1).1

theorem positive_regular_low_normalized_obstruction {lam : ℝ} {z : ℂ} {r p : ℕ}
    (hlam : 0 < lam) (hz : z ∈ regularBoundaryF002 lam (omegaL lam))
    (hr : 0 < r) (hrp : 2 * r < p) (hcop : r.Coprime p) (hp : Odd p)
    (hinc : spectralA lam z = spectralS z * (Real.cos (regularRationalAngle r p) : ℂ) + spectralT lam z)
    (hdet : 0 < spectralDetF002 lam z) :
    ¬ HasDomainExtension (omegaL lam) (lowNormalizedBulk lam) z := by
  apply original_low_nonextension_of_canonical hlam hz
  exact (positive_canonical_both_parities_no_extension hlam hz.2.1 hr hrp hcop hp hinc hdet
    (isOpen_omegaLF002 hlam) (omegaLF002_subset_complement hlam)
    (fun w hw => (endpoint_boundary_criterion hlam).1 (frontier_omegaLF002_subset_endpoint hlam hw)) hz.1).2

end
end IsingBulk.AnisoF002.RegularTail.C03
