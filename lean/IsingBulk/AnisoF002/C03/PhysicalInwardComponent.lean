import IsingBulk.AnisoF002.C03.PhysicalRegularChart
import Mathlib.Analysis.Complex.Convex

/-!
# Actual physical-domain membership of the regular inward inverse

A whole upper half disk of a genuine local inverse lies in the physical
component whose frontier contains its center.  The proof uses the exact
spectral side and connectedness, not a chosen point or an added inward
membership premise.  It applies to both original physical domains.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set Filter IsingBulk.Anisotropic IsingBulk.AnisoF002.Geometry
open scoped Topology

theorem local_inverse_upper_half_ball_subset_domain {D C : Set ℂ} {T Z : ℂ → ℂ} {z : ℂ}
    (hD : IsOpen D) (hDC : D ⊆ C) (hfront : frontier D ⊆ Cᶜ) (hz : z ∈ frontier D)
    (hT : ContinuousAt T z) (hT0 : T z = 0) (hZ : AnalyticAt ℂ Z 0) (hZ0 : Z 0 = z)
    (hright : ∀ᶠ t in 𝓝 (0 : ℂ), T (Z t) = t)
    (hleft : ∀ᶠ w in 𝓝 z, Z (T w) = w)
    (hside : ∀ᶠ w in 𝓝 z, w ∈ C ↔ 0 < (T w).im) :
    ∃ r : ℝ, 0 < r ∧ ∀ t ∈ Metric.ball (0 : ℂ) r, 0 < t.im → Z t ∈ D := by
  have hZside : ∀ᶠ t in 𝓝 (0 : ℂ), Z t ∈ C ↔ 0 < (T (Z t)).im := by
    have hh : ∀ᶠ w in 𝓝 (Z 0), w ∈ C ↔ 0 < (T w).im := by
      simpa only [hZ0] using hside
    exact hZ.continuousAt.eventually hh
  have hnear : ∀ᶠ t in 𝓝 (0 : ℂ), AnalyticAt ℂ Z t ∧ (Z t ∈ C ↔ 0 < t.im) := by
    filter_upwards [hZ.eventually_analyticAt, hZside, hright] with t ht hs hr
    exact ⟨ht, by rwa [hr] at hs⟩
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hnear
  let K : Set ℂ := Metric.ball (0 : ℂ) r ∩ {t : ℂ | 0 < t.im}
  have hK : IsPreconnected K := ((convex_ball (0 : ℂ) r).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hcont : ContinuousOn Z K := fun t ht =>
    (hball (Metric.mem_ball.mp ht.1)).1.continuousAt.continuousWithinAt
  have hP : IsPreconnected (Z '' K) := hK.image Z hcont
  have hPC : Z '' K ⊆ C := by
    rintro w ⟨t, ht, rfl⟩
    exact (hball (Metric.mem_ball.mp ht.1)).2.mpr ht.2
  have hTb : ∀ᶠ w in 𝓝 z, T w ∈ Metric.ball (0 : ℂ) r := by
    apply hT.eventually
    rw [hT0]
    exact Metric.ball_mem_nhds _ hr
  obtain ⟨U, hU, hUopen, hzU⟩ := mem_nhds_iff.mp (hleft.and (hside.and hTb))
  obtain ⟨w, hwU, hwD⟩ := mem_closure_iff.mp hz.1 U hUopen hzU
  have hwT : T w ∈ K := ⟨(hU hwU).2.2, (hU hwU).2.1.mp (hDC hwD)⟩
  have hwP : w ∈ Z '' K := ⟨T w, hwT, (hU hwU).1⟩
  have hPD : Z '' K ⊆ D := by
    apply hP.subset_of_closure_inter_subset hD ⟨w, hwP, hwD⟩
    intro v hv
    by_contra hvD
    have hvF : v ∈ frontier D := by
      refine ⟨hv.1, ?_⟩
      rwa [hD.interior_eq]
    exact hfront hvF (hPC hv.2)
  exact ⟨r, hr, fun t ht hi => hPD ⟨t, ⟨ht, hi⟩, rfl⟩⟩

theorem local_inverse_inward_mem_domain {D C : Set ℂ} {T Z : ℂ → ℂ} {z : ℂ}
    (hD : IsOpen D) (hDC : D ⊆ C) (hfront : frontier D ⊆ Cᶜ) (hz : z ∈ frontier D)
    (hT : ContinuousAt T z) (hT0 : T z = 0) (hZ : AnalyticAt ℂ Z 0) (hZ0 : Z 0 = z)
    (hright : ∀ᶠ t in 𝓝 (0 : ℂ), T (Z t) = t)
    (hleft : ∀ᶠ w in 𝓝 z, Z (T w) = w)
    (hside : ∀ᶠ w in 𝓝 z, w ∈ C ↔ 0 < (T w).im) :
    ∀ᶠ eps : ℝ in 𝓝[>] (0 : ℝ), Z ((eps : ℂ) * Complex.I) ∈ D := by
  obtain ⟨r, hr, hball⟩ := local_inverse_upper_half_ball_subset_domain hD hDC hfront hz
    hT hT0 hZ hZ0 hright hleft hside
  filter_upwards [self_mem_nhdsWithin, (gt_mem_nhds hr).filter_mono nhdsWithin_le_nhds] with eps he her
  apply hball _ ?_ ?_
  · rw [Metric.mem_ball, dist_zero_right, inward_parameter_norm he.le]
    exact her
  · simpa using he

theorem positive_physical_coordinate_side {lam b : ℝ} {z : ℂ}
    (hx : z.re ≠ 0) (hb : |b| < 1)
    (hinc : spectralA lam z = spectralS z * (b : ℂ) + spectralT lam z)
    (hdet : 0 < spectralDetF002 lam z) :
    ∀ᶠ w in 𝓝 z, w ∉ spectralSetF002 lam ↔ 0 < (positiveParameterF002 lam b w).im := by
  have hS := spectralS_ne_zero_of_re_ne_zero hx
  have hs := eventually_signed_side_of_incidence hdet.ne' hS hb (Or.inl rfl)
    (show spectralA lam z = spectralS z * (b : ℂ) + spectralT lam z * (1 : ℂ) by simpa using hinc)
  have hd := (continuous_spectralDetF002 lam).continuousAt.eventually (Ioi_mem_nhds hdet)
  filter_upwards [hs, hd] with w hw hwd
  rw [hw, not_le]
  simp only [one_mul, positiveParameterF002, Complex.sub_im, Complex.ofReal_im, sub_zero]
  exact mul_pos_iff_of_pos_left hwd

theorem positive_physical_chart_inward_domain {lam b : ℝ} {z : ℂ} {Z : ℂ → ℂ} {D : Set ℂ}
    (hx : z.re ≠ 0) (hb : |b| < 1)
    (hinc : spectralA lam z = spectralS z * (b : ℂ) + spectralT lam z)
    (hdet : 0 < spectralDetF002 lam z)
    (hD : IsOpen D) (hDC : D ⊆ (spectralSetF002 lam)ᶜ)
    (hfront : frontier D ⊆ spectralSetF002 lam) (hz : z ∈ frontier D)
    (hZ : AnalyticAt ℂ Z 0) (hZ0 : Z 0 = z)
    (hright : ∀ᶠ t in 𝓝 (0 : ℂ), positiveParameterF002 lam b (Z t) = t)
    (hleft : ∀ᶠ w in 𝓝 z, Z (positiveParameterF002 lam b w) = w) :
    ∀ᶠ eps : ℝ in 𝓝[>] (0 : ℝ), Z ((eps : ℂ) * Complex.I) ∈ D := by
  have hS := spectralS_ne_zero_of_re_ne_zero hx
  apply local_inverse_inward_mem_domain hD hDC (by simpa only [compl_compl] using hfront) hz
    ((analyticAt_edgeCoordinateF002 (e := 1) hS).sub analyticAt_const).continuousAt
    (positiveParameterF002_center hS hinc) hZ hZ0 hright hleft
  exact positive_physical_coordinate_side hx hb hinc hdet

end
end IsingBulk.AnisoF002.RegularTail.C03
