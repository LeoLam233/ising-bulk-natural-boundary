import IsingBulk.AnisoF002.C03.PhysicalNegativeLTChart
import IsingBulk.AnisoF002.C03.PhysicalNegativeCoefficient
import IsingBulk.AnisoF002.C03.NegativeBoundaryJets

/-!
# The actual negative-temperature inverse enters the physical component

The inverse uses t=(edgeCoordinate-cos(phi))/B.  At t=-eps the genuine
endpoint coordinate is -eps B(t), whose imaginary part is positive.
The whole upper-half-disk component theorem therefore identifies this
inward path with the original physical domain.  No domain-side premise
is left in the constructed chart.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set Filter IsingBulk.Anisotropic IsingBulk.AnisoF002.Geometry
  IsingBulk.AnisoF002.NegativeHT
open scoped Topology BigOperators

theorem negative_physical_chart_inward_domain {lam c : ℝ} {z : ℂ}
    {Z B : ℂ → ℂ} {D : Set ℂ}
    (hlam : 0 < lam) (hx : z.re ≠ 0) (hc : |c| < 1)
    (hinc : spectralA lam z = spectralS z * (c : ℂ) - spectralT lam z)
    (hdet : spectralDetF002 lam z < 0)
    (hD : IsOpen D) (hDC : D ⊆ (spectralSetF002 lam)ᶜ)
    (hfront : frontier D ⊆ spectralSetF002 lam) (hz : z ∈ frontier D)
    (hZa : AnalyticAt ℂ Z 0) (hZ0 : Z 0 = z) (hBa : AnalyticAt ℂ B 0)
    (hB : ∀ t, B t = spectralT lam (Z t) / spectralS (Z t))
    (hright : ∀ᶠ t in 𝓝 (0 : ℂ), negativeParameterF002 lam c (Z t) = t) :
    ∀ᶠ eps : ℝ in 𝓝[>] (0 : ℝ), Z (-(eps : ℂ)) ∈ D := by
  have hS := spectralS_ne_zero_of_re_ne_zero hx
  have hT := ((analyticAt_edgeCoordinateF002 (lam := lam) (e := -1) hS).sub
    (analyticAt_const (v := (c : ℂ)))).continuousAt
  obtain ⟨W, _, _, hWa, hW0, _, _, _, _, hWchart, hWleft⟩ :=
    exists_negativeLT_physical_edge_control hlam hx hc hinc hdet
  obtain ⟨r, hr, hupper⟩ := local_inverse_upper_half_ball_subset_domain hD hDC
    (by simpa only [compl_compl] using hfront) hz hT
    (negativeLTParameterF002_center hS hinc) hWa hW0
    (hWchart.mono fun _ h => h.1) hWleft
    (negativeLT_physical_coordinate_side hx hc hinc hdet)
  have hBi : (B 0).im < 0 := by
    rw [hB 0, hZ0]
    change (spectralRatioF002 lam z).im < 0
    rw [spectralRatioF002_im]
    exact div_neg_of_neg_of_pos hdet (Complex.normSq_pos.mpr hS)
  have hBne : B 0 ≠ 0 := by
    intro he
    simp only [he, Complex.zero_im, lt_self_iff_false] at hBi
  have hTU : ∀ᶠ t in 𝓝 (0 : ℂ), negativeLTParameterF002 lam c (Z t) ∈ Metric.ball (0 : ℂ) r := by
    have ht : ContinuousAt (fun t => negativeLTParameterF002 lam c (Z t)) 0 :=
      hT.comp_of_eq hZa.continuousAt hZ0
    apply ht.eventually
    change ∀ᶠ y in 𝓝 (negativeLTParameterF002 lam c (Z 0)), y ∈ Metric.ball (0 : ℂ) r
    rw [hZ0, negativeLTParameterF002_center hS hinc]
    exact Metric.ball_mem_nhds _ hr
  have hleft : ∀ᶠ t in 𝓝 (0 : ℂ), W (negativeLTParameterF002 lam c (Z t)) = Z t := by
    have hh : ∀ᶠ w in 𝓝 (Z 0), W (negativeLTParameterF002 lam c w) = w := by
      simpa only [hZ0] using hWleft
    exact hZa.continuousAt.eventually hh
  have hlocal : ∀ᶠ t in 𝓝 (0 : ℂ),
      negativeLTParameterF002 lam c (Z t) = B t * t ∧
      (B t).im < 0 ∧ negativeLTParameterF002 lam c (Z t) ∈ Metric.ball (0 : ℂ) r ∧
      W (negativeLTParameterF002 lam c (Z t)) = Z t := by
    filter_upwards [hright, hBa.continuousAt.eventually_ne hBne,
      (Complex.continuous_im.continuousAt.comp hBa.continuousAt).eventually (Iio_mem_nhds hBi),
      hTU, hleft] with t ht hbn hbi hball hl
    refine ⟨?_, hbi, hball, hl⟩
    change negativeLTParameterF002 lam c (Z t) / spectralRatioF002 lam (Z t) = t at ht
    have hBt : B t = spectralRatioF002 lam (Z t) := hB t
    rw [← hBt] at ht
    exact ((div_eq_iff hbn).mp ht).trans (mul_comm _ _)
  have hp : Tendsto (fun eps : ℝ => -(eps : ℂ)) (𝓝 (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    convert (show ContinuousAt (fun eps : ℝ => -(eps : ℂ)) 0 by fun_prop).tendsto using 1
    simp
  filter_upwards [self_mem_nhdsWithin, (hp.eventually hlocal).filter_mono nhdsWithin_le_nhds]
    with eps he hl
  rw [← hl.2.2.2]
  apply hupper _ hl.2.2.1
  rw [hl.1]
  simp only [Complex.mul_im, Complex.neg_re, Complex.ofReal_re, Complex.neg_im,
    Complex.ofReal_im, neg_zero, mul_zero, zero_add]
  exact mul_pos_of_neg_of_neg hl.2.1 (neg_neg_of_pos he)

theorem exists_negative_original_odd_chart {lam φ : ℝ} {z : ℂ}
    (hlam : 0 < lam) (hz : z ∈ regularBoundaryF002 lam (omegaH lam))
    (hφ : 0 < φ) (hπ : φ < Real.pi)
    (hinc : spectralA lam z = spectralS z * (Real.cos φ : ℂ) + spectralT lam z * (-1))
    (hdet : spectralDetF002 lam z < 0) :
    ∃ Z B : ℂ → ℂ, AnalyticAt ℂ Z 0 ∧ Z 0 = z ∧ AnalyticAt ℂ B 0 ∧
      B 0 = spectralT lam z / spectralS z ∧ (B 0).im < 0 ∧
      (∀ t, B t = spectralT lam (Z t) / spectralS (Z t)) ∧
      (∀ᶠ eps : ℝ in 𝓝[>] (0 : ℝ), Z (-(eps : ℂ)) ∈ omegaH lam) ∧
      ∀ b : ℂ → ℂ, AnalyticAt ℂ b 0 → (∀ t, b t ^ 2 = B t) →
        ∀ᶠ eps : ℝ in 𝓝[>] (0 : ℝ),
          (fun u => canonicalAngularTailF002 lam 0 (Z u)) =ᶠ[𝓝 (-(eps : ℂ))]
            fun u => (Complex.sqrt (B 0) / b 0) * negativePhysicalOddSum b B φ u := by
  have hc := abs_cos_lt_one_of_sin_ne_zero
    (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hφ hπ))
  obtain ⟨Z, B, hZa, hZ0, hBa, hB0, _, hB, hchart, _⟩ :=
    exists_negative_physical_chart hlam hz.2.1 hc hinc
  have hBi : (B 0).im < 0 := by
    rw [hB0]
    change (spectralRatioF002 lam z).im < 0
    rw [spectralRatioF002_im]
    exact div_neg_of_neg_of_pos hdet (Complex.normSq_pos.mpr (spectralS_ne_zero_of_re_ne_zero hz.2.1))
  obtain ⟨d⟩ := exists_negative_coefficient_control hBa hφ hπ hBi
  have hside := negative_physical_chart_inward_domain hlam hz.2.1 hc
    (by simpa only [mul_neg_one, sub_eq_add_neg] using hinc) hdet
    (isOpen_omegaHF002 hlam) (omegaHF002_subset_complement hlam)
    (fun w hw => (endpoint_boundary_criterion hlam).1 (frontier_omegaHF002_subset_endpoint hlam hw))
    hz.1 hZa hZ0 hBa hB (hchart.mono fun _ h => h.1)
  refine ⟨Z, B, hZa, hZ0, hBa, hB0, hBi, hB, hside, ?_⟩
  intro b hba hbsq
  have hg := exists_negative_physical_coefficient_germs d hBa hba hBi hbsq hB
    (hchart.mono fun _ h => ⟨h.2.1, h.2.2.2⟩)
  filter_upwards [hg] with eps he
  exact he.mono fun _ h => h.2

end
end IsingBulk.AnisoF002.RegularTail.C03
