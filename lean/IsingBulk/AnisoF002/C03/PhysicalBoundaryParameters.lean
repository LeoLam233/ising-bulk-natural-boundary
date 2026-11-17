import IsingBulk.AnisoF002.C03.PhysicalInwardComponent
import IsingBulk.AnisoF002.C03.RegularDensity

/-!
# Actual real parameter intervals in a regular physical frontier

The local inverse maps the real parameter interval into the same physical
frontier, because its entire upper half disk lies in that component and
the real interval itself lies in the spectral set.  The endpoint
coordinate and every regularity condition are retained on one interval.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open IsingBulk.Anisotropic IsingBulk.AnisoF002.Geometry IsingBulk.AnisoF002.NegativeHT
  Set Filter
open scoped Topology

theorem local_inverse_real_interval_frontier {D C : Set ℂ} {T Z : ℂ → ℂ} {z : ℂ}
    (hD : IsOpen D) (hDC : D ⊆ C) (hfront : frontier D ⊆ Cᶜ) (hz : z ∈ frontier D)
    (hT : ContinuousAt T z) (hT0 : T z = 0) (hZ : AnalyticAt ℂ Z 0) (hZ0 : Z 0 = z)
    (hright : ∀ᶠ t in 𝓝 (0 : ℂ), T (Z t) = t)
    (hleft : ∀ᶠ w in 𝓝 z, Z (T w) = w)
    (hside : ∀ᶠ w in 𝓝 z, w ∈ C ↔ 0 < (T w).im) :
    ∃ r : ℝ, 0 < r ∧ ∀ v : ℝ, |v| < r → Z (v : ℂ) ∈ frontier D := by
  obtain ⟨r, hr, hupper⟩ := local_inverse_upper_half_ball_subset_domain hD hDC hfront hz
    hT hT0 hZ hZ0 hright hleft hside
  have hZside : ∀ᶠ t in 𝓝 (0 : ℂ), Z t ∈ C ↔ 0 < (T (Z t)).im := by
    have hh : ∀ᶠ w in 𝓝 (Z 0), w ∈ C ↔ 0 < (T w).im := by simpa only [hZ0] using hside
    exact hZ.continuousAt.eventually hh
  have hnear : ∀ᶠ t in 𝓝 (0 : ℂ), AnalyticAt ℂ Z t ∧ (Z t ∈ C ↔ 0 < t.im) := by
    filter_upwards [hZ.eventually_analyticAt, hZside, hright] with t ht hs hright
    exact ⟨ht, by rwa [hright] at hs⟩
  obtain ⟨s, hs, hlocal⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨min r s, lt_min hr hs, ?_⟩
  intro v hv
  have hvr : (v : ℂ) ∈ Metric.ball (0 : ℂ) r := by
    simpa only [Metric.mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] using
      hv.trans_le (min_le_left _ _)
  have hvs : dist (v : ℂ) 0 < s := by
    simpa only [dist_zero_right, Complex.norm_real, Real.norm_eq_abs] using
      hv.trans_le (min_le_right _ _)
  have hp : Tendsto (fun eps : ℝ => (v : ℂ) + (eps : ℂ) * Complex.I)
      (𝓝[>] (0 : ℝ)) (𝓝 (v : ℂ)) := by
    have hc : Continuous (fun eps : ℝ => (v : ℂ) + (eps : ℂ) * Complex.I) := by fun_prop
    simpa only [Complex.ofReal_zero, zero_mul, add_zero] using
      (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  have hlim := (hlocal hvs).1.continuousAt.tendsto.comp hp
  have hball := hp.eventually (Metric.isOpen_ball.mem_nhds hvr)
  have hin : ∀ᶠ eps : ℝ in 𝓝[>] (0 : ℝ), Z ((v : ℂ) + (eps : ℂ) * Complex.I) ∈ D := by
    filter_upwards [self_mem_nhdsWithin, hball] with eps he hb
    apply hupper _ hb
    simpa using he
  refine ⟨mem_closure_of_tendsto hlim hin, ?_⟩
  rw [hD.interior_eq]
  intro hvD
  have hh := (hlocal hvs).2.mp (hDC hvD)
  simp only [Complex.ofReal_im, lt_self_iff_false] at hh

theorem physical_endpoint_constant_side {lam b e : ℝ} {z : ℂ}
    (hx : z.re ≠ 0) (hb : |b| < 1) (he : e = 1 ∨ e = -1)
    (hinc : spectralA lam z = spectralS z * (b : ℂ) + spectralT lam z * (e : ℂ))
    (hdet : spectralDetF002 lam z ≠ 0) :
    ∀ᶠ w in 𝓝 z, w ∉ spectralSetF002 lam ↔
      0 < (((e * spectralDetF002 lam z : ℝ) : ℂ) * (edgeCoordinateF002 lam e w - (b : ℂ))).im := by
  have hS := spectralS_ne_zero_of_re_ne_zero hx
  have henz : e ≠ 0 := by rcases he with rfl | rfl <;> norm_num
  have ha : e * spectralDetF002 lam z ≠ 0 := mul_ne_zero henz hdet
  have hs := eventually_signed_side_of_incidence hdet hS hb he hinc
  have hc : ContinuousAt (fun w => e * spectralDetF002 lam w) z :=
    continuous_const.continuousAt.mul (continuous_spectralDetF002 lam).continuousAt
  rcases lt_or_gt_of_ne ha with hn | hp
  · filter_upwards [hs, hc.eventually (Iio_mem_nhds hn)] with w hw hwd
    rw [hw, not_le]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im,
      sub_zero, zero_mul, add_zero]
    simp only [mul_pos_iff, not_lt.mpr hwd.le, hwd, not_lt.mpr hn.le, hn,
      false_and, false_or, true_and]
  · filter_upwards [hs, hc.eventually (Ioi_mem_nhds hp)] with w hw hwd
    rw [hw, not_le]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im,
      sub_zero, zero_mul, add_zero]
    exact (mul_pos_iff_of_pos_left hwd).trans (mul_pos_iff_of_pos_left hp).symm

theorem exists_regular_first_boundary_parameters {lam : ℝ} {z : ℂ} {D : Set ℂ}
    (hlam : 0 < lam) (hz : z ∈ regularBoundaryF002 lam D)
    (hD : IsOpen D) (hDC : D ⊆ (spectralSetF002 lam)ᶜ)
    (hfront : frontier D ⊆ spectralSetF002 lam)
    (hf : geometryF1 lam z.re z.im = 0) (hg : geometryF2 lam z.re z.im ≠ 0) :
    ∃ (b e : ℝ) (ψ : ℝ → ℂ), |b| < 1 ∧ (e = 1 ∨ e = -1) ∧
      ContinuousAt ψ b ∧ ψ b = z ∧
      ∀ᶠ u in 𝓝 b, ψ u ∈ regularBoundaryF002 lam D ∧ spectralDetF002 lam (ψ u) ≠ 0 ∧
        spectralA lam (ψ u) = spectralS (ψ u) * (u : ℂ) + spectralT lam (ψ u) * (e : ℂ) := by
  obtain ⟨b, e, hb, he, hinc, hdet, hcoord, hd, hd0, _⟩ :=
    regular_first_endpoint_chart_all_re hlam hz.2.1 hf hg
  let α : ℝ := e * spectralDetF002 lam z
  have henz : e ≠ 0 := by rcases he with rfl | rfl <;> norm_num
  have hα : α ≠ 0 := mul_ne_zero henz hdet
  have hαc : (α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hα
  let T : ℂ → ℂ := fun w => (α : ℂ) * (edgeCoordinateF002 lam e w - (b : ℂ))
  have hS := spectralS_ne_zero_of_re_ne_zero hz.2.1
  have hTa : AnalyticAt ℂ T z := analyticAt_const.mul
    ((analyticAt_edgeCoordinateF002 hS).sub analyticAt_const)
  have hTd : HasDerivAt T ((α : ℂ) * edgeDerivativeF002 lam e z) z :=
    (hd.sub_const _).const_mul _
  have hT0 : T z = 0 := by simp only [T, hcoord, sub_self, mul_zero]
  obtain ⟨Z, hZa, hZ0, _, hright, hleft⟩ := exists_local_analytic_inverse_zero
    hTa hTd (mul_ne_zero hαc hd0) hT0
  obtain ⟨R, hR, hboundary⟩ := local_inverse_real_interval_frontier hD hDC
    (by simpa only [compl_compl] using hfront) hz.1 hTa.continuousAt hT0 hZa hZ0 hright hleft
    (physical_endpoint_constant_side hz.2.1 hb he hinc hdet)
  let ψ : ℝ → ℂ := fun u => Z ((α : ℂ) * ((u : ℂ) - b))
  have hψ0 : ψ b = z := by simp only [ψ, sub_self, mul_zero, hZ0]
  have harg : Tendsto (fun u : ℝ => (α : ℂ) * ((u : ℂ) - b)) (𝓝 b) (𝓝 (0 : ℂ)) := by
    have hc : Continuous (fun u : ℝ => (α : ℂ) * ((u : ℂ) - b)) := by fun_prop
    simpa only [sub_self, mul_zero] using (hc.continuousAt (x := b)).tendsto
  have hψ : ContinuousAt ψ b := by
    rw [ContinuousAt, hψ0]
    simpa only [ψ, Function.comp_def, hZ0] using hZa.continuousAt.tendsto.comp harg
  have hreal : ∀ᶠ u in 𝓝 b, |α * (u - b)| < R := by
    have hc : ContinuousAt (fun u : ℝ => |α * (u - b)|) b := by fun_prop
    have hh : |α * (b - b)| < R := by simpa using hR
    exact hc.eventually (gt_mem_nhds hh)
  have hdetNear : ∀ᶠ u in 𝓝 b, spectralDetF002 lam (ψ u) ≠ 0 :=
    ((continuous_spectralDetF002 lam).continuousAt.comp hψ).eventually_ne (by simpa only [Function.comp_def, hψ0] using hdet)
  have hxNear : ∀ᶠ u in 𝓝 b, (ψ u).re ≠ 0 :=
    (Complex.continuous_re.continuousAt.comp hψ).eventually_ne (by simpa only [Function.comp_def, hψ0] using hz.2.1)
  have hpNear : ∀ᶠ u in 𝓝 b, profileDifferenceF002 lam (ψ u).im ≠ 0 := by
    have hi : ContinuousAt (fun u : ℝ => (ψ u).im) b :=
      Complex.continuous_im.continuousAt.comp (f := ψ) hψ
    have hc : ContinuousAt (fun u : ℝ => profileDifferenceF002 lam (ψ u).im) b :=
      (profileDifference_analyticAt hlam (ψ b).im).continuousAt.comp
        (f := fun u : ℝ => (ψ u).im) hi
    exact hc.eventually_ne (by simpa only [hψ0] using hz.2.2)
  refine ⟨b, e, ψ, hb, he, hψ, hψ0, ?_⟩
  filter_upwards [harg.eventually hright, hreal, hdetNear, hxNear, hpNear] with u hu hur hud hux hup
  have hfro : ψ u ∈ frontier D := by
    simpa only [ψ, Complex.ofReal_mul, Complex.ofReal_sub] using hboundary (α * (u - b)) hur
  refine ⟨⟨hfro, hux, hup⟩, hud, ?_⟩
  have hc : edgeCoordinateF002 lam e (ψ u) = (u : ℂ) := by
    change (α : ℂ) * (edgeCoordinateF002 lam e (ψ u) - b) = (α : ℂ) * ((u : ℂ) - b) at hu
    have hh := mul_left_cancel₀ hαc hu
    linear_combination hh
  have hSu := spectralS_ne_zero_of_re_ne_zero hux
  unfold edgeCoordinateF002 at hc
  have hh := (div_eq_iff hSu).mp hc
  linear_combination hh

end
end IsingBulk.AnisoF002.RegularTail.C03
