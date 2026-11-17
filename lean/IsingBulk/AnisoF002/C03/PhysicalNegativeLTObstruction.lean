import IsingBulk.AnisoF002.C03.PhysicalNegativeLTChart
import IsingBulk.AnisoF002.C03.PhysicalEvenAngleShift
import IsingBulk.AnisoF002.C03.PhysicalPositiveObstruction

/-!
# The full original low-temperature obstruction at the negative endpoint

Every even physical coefficient, and hence the complete even series, is
identified on a single inward germ after the exact torus translation.
The full first singularity is then transferred to the original chosen
prefactor and exact physical domain.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open IsingBulk.Anisotropic IsingBulk.Anisotropic.FormFactors IsingBulk.AnisoF002.Geometry
  Filter Set
open scoped Topology

theorem negativeLT_even_corresponding_inward_germs {lam b : ℝ} {Z B : ℂ → ℂ}
    (d : RegularEdgeCompleteControl b B) (hZa : AnalyticAt ℂ Z 0)
    (hB : ∀ t, B t = -(spectralT lam (Z t) / spectralS (Z t)))
    (hchart : ∀ᶠ t in 𝓝 0, spectralS (Z t) ≠ 0 ∧
      ∀ q : ℂ, (spectralA lam (Z t) - spectralT lam (Z t) * Complex.cos (q + Real.pi)) /
        spectralS (Z t) = affineEdgeCenter b t + B t * (1 - Complex.cos q))
    (hside : ∀ᶠ eps : ℝ in 𝓝[>] (0 : ℝ), Z ((eps : ℂ) * Complex.I) ∉ spectralSetF002 lam) :
    ∀ᶠ eps : ℝ in 𝓝[>] (0 : ℝ),
      edgeParticleTail (affineEdgeCenter b) B 1 =ᶠ[𝓝 ((eps : ℂ) * Complex.I)]
        fun u => canonicalAngularTailF002 lam 1 (Z u) := by
  obtain ⟨s, hs, hlocal⟩ := Metric.eventually_nhds_iff.mp (hchart.and hZa.eventually_analyticAt)
  let eps1 := min d.eps0 (s / 2)
  have heps1 : 0 < eps1 := lt_min d.eps0_pos (half_pos hs)
  filter_upwards [self_mem_nhdsWithin, hside,
    (gt_mem_nhds heps1).filter_mono nhdsWithin_le_nhds] with eps he hz he1
  have he0 : eps ≤ d.eps0 := he1.le.trans (min_le_left _ _)
  have ht : (eps : ℂ) * Complex.I ∈ Metric.ball (0 : ℂ) s := by
    rw [Metric.mem_ball, dist_zero_right, inward_parameter_norm he.le]
    exact (he1.le.trans (min_le_right _ _)).trans_lt (half_lt_self hs)
  have hzNear : ∀ᶠ u in 𝓝 ((eps : ℂ) * Complex.I), Z u ∉ spectralSetF002 lam :=
    (hlocal (Metric.mem_ball.mp ht)).2.continuousAt.eventually
      ((isClosed_spectralSetF002 lam).isOpen_compl.mem_nhds hz)
  obtain ⟨r, eta, hr, heta, _, hprot⟩ := d.exists_inward_common_pole_disk he he0
  filter_upwards [Metric.isOpen_ball.mem_nhds ht,
    Metric.closedBall_mem_nhds ((eps : ℂ) * Complex.I) hr, hzNear] with u hu hur huz
  have hc := (hlocal (Metric.mem_ball.mp hu)).1
  have hp := hprot u hur
  have hphase (q : ℝ) : 0 < (edgeAnglePhase (affineEdgeCenter b) B u q).re := by
    have hh := (half_pos heta).trans_le (hp.2 1 (by norm_num) (fun _ => q))
    simpa [edgeTotalPhase] using hh
  have hroot := negativeLT_edgeAngleRoot_eq_canonical hc.1 hc.2 hphase
  unfold edgeParticleTail canonicalAngularTailF002
  apply tsum_congr
  intro n
  exact edgeParticleCoefficient_eq_canonical_even_pi
    (show Even (1 + 2 * n + 1) from ⟨n + 1, by omega⟩) huz (hB u) hroot

theorem negativeLT_canonical_even_no_extension {lam : ℝ} {z : ℂ} {r p : ℕ} {D : Set ℂ}
    (hlam : 0 < lam) (hx : z.re ≠ 0)
    (hr : 0 < r) (hrp : 2 * r < p) (hcop : r.Coprime p) (hp : Odd p)
    (hinc : spectralA lam z = spectralS z * (Real.cos (regularRationalAngle r p) : ℂ) - spectralT lam z)
    (hdet : spectralDetF002 lam z < 0)
    (hD : IsOpen D) (hDC : D ⊆ (spectralSetF002 lam)ᶜ)
    (hfront : frontier D ⊆ spectralSetF002 lam) (hz : z ∈ frontier D) :
    ¬ HasDomainExtension D (canonicalAngularTailF002 lam 1) z := by
  have hb := regularRational_cos_abs_lt_one hr hrp
  obtain ⟨Z, B, d, hZa, hZ0, _, _, hB0, hB, hchart, hleft⟩ :=
    exists_negativeLT_physical_edge_control hlam hx hb hinc hdet
  have hBi : 0 < (B 0).im := by
    rw [hB0]
    change 0 < (-spectralRatioF002 lam z).im
    rw [Complex.neg_im, spectralRatioF002_im]
    exact neg_pos.mpr (div_neg_of_neg_of_pos hdet
      (Complex.normSq_pos.mpr (spectralS_ne_zero_of_re_ne_zero hx)))
  have hside := negativeLT_physical_chart_inward_domain hx hb hinc hdet hD hDC hfront hz
    hZa hZ0 (hchart.mono fun _ h => h.1) hleft
  have hcor := negativeLT_even_corresponding_inward_germs d hZa hB
    (hchart.mono fun _ h => h.2) (hside.mono fun _ h => hDC h)
  exact no_extension_of_corresponding_inward_germs hD hZa hZ0 hside hcor
    (d.rational_even_series_no_analytic_inward_germ hr hrp hcop hp hBi)

theorem negative_regular_low_normalized_obstruction {lam : ℝ} {z : ℂ} {r p : ℕ}
    (hlam : 0 < lam) (hz : z ∈ regularBoundaryF002 lam (omegaL lam))
    (hr : 0 < r) (hrp : 2 * r < p) (hcop : r.Coprime p) (hp : Odd p)
    (hinc : spectralA lam z = spectralS z * (Real.cos (regularRationalAngle r p) : ℂ) - spectralT lam z)
    (hdet : spectralDetF002 lam z < 0) :
    ¬ HasDomainExtension (omegaL lam) (lowNormalizedBulk lam) z := by
  apply original_low_nonextension_of_canonical hlam hz
  exact negativeLT_canonical_even_no_extension hlam hz.2.1 hr hrp hcop hp hinc hdet
    (isOpen_omegaLF002 hlam) (omegaLF002_subset_complement hlam)
    (fun w hw => (endpoint_boundary_criterion hlam).1 (frontier_omegaLF002_subset_endpoint hlam hw)) hz.1

end
end IsingBulk.AnisoF002.RegularTail.C03
