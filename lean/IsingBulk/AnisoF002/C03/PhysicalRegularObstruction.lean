import IsingBulk.AnisoF002.C03.RegularFirstObstruction
import IsingBulk.AnisoF002.C03.PhysicalRegularTail

/-!
# The complete regular odd obstruction on the actual spectral inverse

The inverse chart and its coefficient are constructed from the literal
physical spectrum.  Canonical angular coefficients agree on open inward
germs at every particle number, so the proved full-series obstruction
transfers to that actual family.  A general domain pullback records the
remaining domain-side membership explicitly.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set Filter IsingBulk.Anisotropic IsingBulk.AnisoF002.Geometry
open scoped Topology

theorem no_extension_of_inward_chart {D : Set ℂ} {F Z : ℂ → ℂ} {z : ℂ}
    (hD : IsOpen D) (hZ : AnalyticAt ℂ Z 0) (hZ0 : Z 0 = z)
    (hside : ∀ᶠ eps : ℝ in 𝓝[>] (0 : ℝ), Z ((eps : ℂ) * Complex.I) ∈ D)
    (hno : ¬ ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧
      ∀ᶠ eps : ℝ in 𝓝[>] (0 : ℝ),
        (fun u => F (Z u)) =ᶠ[𝓝 ((eps : ℂ) * Complex.I)] g) :
    ¬ HasDomainExtension D F z := by
  rintro ⟨U, hU, hzU, g, hg, heq⟩
  apply hno
  refine ⟨fun u => g (Z u), (hg z hzU).comp_of_eq hZ hZ0, ?_⟩
  have hp : Tendsto (fun eps : ℝ => (eps : ℂ) * Complex.I) (𝓝 (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    convert (show ContinuousAt (fun eps : ℝ => (eps : ℂ) * Complex.I) 0 by fun_prop).tendsto using 1
    simp
  have hmem : ∀ᶠ y in 𝓝 (Z 0), y ∈ U := by rw [hZ0]; exact hU.mem_nhds hzU
  have hZU : ∀ᶠ u in 𝓝 (0 : ℂ), Z u ∈ U := hZ.continuousAt.eventually hmem
  have hnear := hp.eventually (hZU.and hZ.eventually_analyticAt)
  filter_upwards [hside, hnear.filter_mono nhdsWithin_le_nhds] with eps heD he
  have hUD := he.2.continuousAt.eventually ((hU.inter hD).mem_nhds ⟨he.1, heD⟩)
  filter_upwards [hUD] with u hu
  exact (heq hu).symm

/-- The actual spectral inverse carries the complete canonical odd
series to a nonextendable inward germ at every rational positive edge.
Physical contour identification is not assumed by this theorem. -/
theorem exists_positive_canonical_odd_obstruction {lam : ℝ} {z : ℂ} {r p : ℕ}
    (hlam : 0 < lam) (hx : z.re ≠ 0)
    (hr : 0 < r) (hrp : 2 * r < p) (hcop : r.Coprime p) (hp : Odd p)
    (hinc : spectralA lam z = spectralS z * (Real.cos (regularRationalAngle r p) : ℂ) +
      spectralT lam z) (hdet : 0 < spectralDetF002 lam z) :
    ∃ Z : ℂ → ℂ, AnalyticAt ℂ Z 0 ∧ Z 0 = z ∧
      HasDerivAt Z (edgeDerivativeF002 lam 1 z)⁻¹ 0 ∧
      (∀ᶠ w in 𝓝 z, Z (positiveParameterF002 lam (Real.cos (regularRationalAngle r p)) w) = w) ∧
      (¬ ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧
        ∀ᶠ eps : ℝ in 𝓝[>] (0 : ℝ),
          (fun u => canonicalAngularTailF002 lam 0 (Z u)) =ᶠ[𝓝 ((eps : ℂ) * Complex.I)] g) ∧
      (∀ D : Set ℂ, IsOpen D →
        (∀ᶠ eps : ℝ in 𝓝[>] (0 : ℝ), Z ((eps : ℂ) * Complex.I) ∈ D) →
          ¬ HasDomainExtension D (canonicalAngularTailF002 lam 0) z) := by
  obtain ⟨Z, B, d, hZa, hZ0, hZd, _, hB0, hB, hchart, hleft⟩ :=
    exists_positive_physical_edge_control hlam hx (regularRational_cos_abs_lt_one hr hrp) hinc hdet
  have hBi : 0 < (B 0).im := by
    rw [hB0]
    change 0 < (spectralRatioF002 lam z).im
    rw [spectralRatioF002_im]
    exact div_pos hdet (Complex.normSq_pos.mpr (spectralS_ne_zero_of_re_ne_zero hx))
  have hno := d.rational_odd_series_no_analytic_inward_germ hr hrp hcop hp hBi
  obtain ⟨eps1, heps1, _, hcanon⟩ := exists_canonical_regular_germs d hB
    (hchart.mono fun _ h => h.2)
  have hcanon' : ∀ᶠ eps : ℝ in 𝓝[>] (0 : ℝ),
      edgeParticleTail (affineEdgeCenter (Real.cos (regularRationalAngle r p))) B 0
        =ᶠ[𝓝 ((eps : ℂ) * Complex.I)] fun u => canonicalAngularTailF002 lam 0 (Z u) := by
    filter_upwards [self_mem_nhdsWithin,
      (gt_mem_nhds heps1).filter_mono nhdsWithin_le_nhds] with eps he he1
    exact (hcanon eps he he1.le).mono fun _ h => h.2 0
  have hno' : ¬ ∃ g : ℂ → ℂ, AnalyticAt ℂ g 0 ∧
      ∀ᶠ eps : ℝ in 𝓝[>] (0 : ℝ),
        (fun u => canonicalAngularTailF002 lam 0 (Z u)) =ᶠ[𝓝 ((eps : ℂ) * Complex.I)] g := by
    rintro ⟨g, hg, heq⟩
    apply hno
    refine ⟨g, hg, ?_⟩
    filter_upwards [hcanon', heq] with eps hc he
    exact hc.trans he
  exact ⟨Z, hZa, hZ0, hZd, hleft, hno', fun D hD hs =>
    no_extension_of_inward_chart hD hZa hZ0 hs hno'⟩

end
end IsingBulk.AnisoF002.RegularTail.C03
