import IsingBulk.AnisoF002.C03.PhysicalRealFactors
import IsingBulk.AnisoF002.C03.PhysicalContourGeometry

/-!
# Actual positive-real anisotropic root on a common complex annulus

The reciprocal root is selected by its quadratic and strict unit-disk norm,
then proved analytic by the F002 implicit-function construction.  Compactness
of the actual unit circle gives a single annulus and interior contour gap
before every particle number and lattice displacement.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open IsingBulk.Anisotropic IsingBulk.Anisotropic.FormFactors IsingBulk.First
open IsingBulk.AnisoF002.Geometry Set Filter Metric
open scoped Topology

def reciprocalInteriorRoot (W : ℂ) : ℂ := by
  classical
  exact if h : ∃ r : ℂ, r ^ 2 - 2 * W * r + 1 = 0 ∧ ‖r‖ < 1 then h.choose else 0

theorem reciprocalInteriorRoot_spec {W : ℂ} (hW : 1 < W.re) :
    reciprocalInteriorRoot W ^ 2 - 2 * W * reciprocalInteriorRoot W + 1 = 0 ∧
      ‖reciprocalInteriorRoot W‖ < 1 := by
  have hn : ¬ ∃ u : ℝ, u ∈ Icc (-1 : ℝ) 1 ∧ W = (u : ℂ) := by
    rintro ⟨u, hu, he⟩
    have hh := congrArg Complex.re he
    simp only [Complex.ofReal_re] at hh
    linarith [hu.2]
  have he := (exists_unique_reciprocal_small_root hn).exists
  simp only [reciprocalInteriorRoot, dite_eq_left he]
  exact he.choose_spec

theorem reciprocalInteriorRoot_ne_zero {W : ℂ} (hW : 1 < W.re) :
    reciprocalInteriorRoot W ≠ 0 := by
  intro he
  have hp := (reciprocalInteriorRoot_spec hW).1
  simp [he] at hp

theorem reciprocalInteriorRoot_analyticAt {W : ℂ} (hW : 1 < W.re) :
    AnalyticAt ℂ reciprocalInteriorRoot W := by
  have hs := reciprocalInteriorRoot_spec hW
  obtain ⟨R, hR, _, he⟩ := exists_joint_analytic_quadratic_root
    1 W (reciprocalInteriorRoot W) (by simpa using hs.1)
    (by simpa using reciprocal_small_root_simple hs.1 hs.2) hs.2
  have ha : AnalyticAt ℂ (fun w : ℂ => R (1, w)) W :=
    hR.comp (analyticAt_const.prod analyticAt_id)
  apply ha.congr
  have hh : ∀ᶠ w in 𝓝 W, (1 : ℂ) * R (1, w) ^ 2 - 2 * w * R (1, w) + 1 = 0 ∧
      ‖R (1, w)‖ < 1 :=
    (continuousAt_const.prodMk continuousAt_id).eventually he
  have hw : ∀ᶠ w in 𝓝 W, 1 < w.re :=
    Complex.continuous_re.continuousAt.eventually (Ioi_mem_nhds hW)
  filter_upwards [hh, hw] with w hr hw
  exact reciprocal_small_root_unique (by simpa using hr.1)
    (reciprocalInteriorRoot_spec hw).1 hr.2 (reciprocalInteriorRoot_spec hw).2

theorem reciprocalInteriorRoot_real {W : ℝ} (hW : 1 < W) :
    reciprocalInteriorRoot (W : ℂ) = (Real.exp (-Real.arcosh W) : ℂ) := by
  have hs := reciprocalInteriorRoot_spec (show 1 < (W : ℂ).re from hW)
  have hr := exp_neg_arcosh_reciprocal_polynomial hW
  refine reciprocal_small_root_unique hs.1 ?_ hs.2 ?_
  · exact_mod_cast hr.1
  · simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr.2.1] using hr.2.2

def physicalAnnularW (B C : ℝ) (y : ℂ) : ℂ :=
  (C : ℂ) - (B : ℂ) * (y + y⁻¹) / 2

def physicalAnnularRoot (B C : ℝ) (y : ℂ) : ℂ :=
  reciprocalInteriorRoot (physicalAnnularW B C y)

theorem physicalAnnularW_analyticAt (B C : ℝ) {y : ℂ} (hy : y ≠ 0) :
    AnalyticAt ℂ (physicalAnnularW B C) y :=
  analyticAt_const.sub ((analyticAt_const.mul (analyticAt_id.add (analyticAt_id.inv hy))).div_const)

theorem physicalAnnularW_unit (B C : ℝ) {y : ℂ} (hy : ‖y‖ = 1) :
    physicalAnnularW B C y = ((C - B * y.re : ℝ) : ℂ) := by
  rw [physicalAnnularW, literal_unit_trace y hy]
  push_cast
  ring

theorem physicalAnnularW_unit_gt_one {B C : ℝ} (hB : 0 ≤ B) (hgap : 1 < C - B)
    {y : ℂ} (hy : ‖y‖ = 1) : 1 < (physicalAnnularW B C y).re := by
  rw [physicalAnnularW_unit B C hy, Complex.ofReal_re]
  have hre : y.re ≤ 1 := (Complex.re_le_norm y).trans hy.le
  have hm := mul_le_mul_of_nonneg_left hre hB
  linarith

theorem physicalAnnularRoot_analyticAt {B C : ℝ} {y : ℂ}
    (hy : y ≠ 0) (hW : 1 < (physicalAnnularW B C y).re) :
    AnalyticAt ℂ (physicalAnnularRoot B C) y :=
  (reciprocalInteriorRoot_analyticAt hW).comp (physicalAnnularW_analyticAt B C hy)

theorem physicalAnnularRoot_unit_angle {B C : ℝ} (hB : 0 ≤ B) (hgap : 1 < C - B)
    (θ : ℝ) : physicalAnnularRoot B C (anglePoint 1 θ) = (FormFactors.root B C θ : ℂ) := by
  have hy : ‖anglePoint 1 θ‖ = 1 := by simp [anglePoint, norm_circleMap_zero]
  have hre : (anglePoint 1 θ).re = Real.cos θ := by
    simp [anglePoint, circleMap_zero_re]
  unfold physicalAnnularRoot
  rw [physicalAnnularW_unit B C hy, hre, reciprocalInteriorRoot_real]
  · rfl
  · have hh := physicalAnnularW_unit_gt_one hB hgap hy
    simpa only [physicalAnnularW_unit B C hy, Complex.ofReal_re, hre] using hh

theorem inner_annulus_subset_open_of_unit_sphere {U : Set ℂ} (hU : IsOpen U)
    (hKU : sphere (0 : ℂ) 1 ⊆ U) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ y : ℂ, r ≤ ‖y‖ → ‖y‖ ≤ 1 → y ∈ U := by
  obtain ⟨δ, hδ, hsub⟩ := (isCompact_sphere (0 : ℂ) 1).exists_thickening_subset_open hU hKU
  let ε := min (δ / 2) (1 / 2 : ℝ)
  have hε : 0 < ε := lt_min (half_pos hδ) (by norm_num)
  have hε1 : ε ≤ 1 / 2 := min_le_right _ _
  have hεδ : ε < δ := (min_le_left _ _).trans_lt (half_lt_self hδ)
  refine ⟨1 - ε, by linarith, by linarith, ?_⟩
  intro y hy hy1
  have hy0 : y ≠ 0 := norm_pos_iff.mp (by linarith)
  obtain ⟨hyn, hyd⟩ := radial_projection_distance hy0 hy1
  apply hsub
  rw [mem_thickening_iff]
  refine ⟨(‖y‖ : ℂ)⁻¹ * y, by simpa using hyn, ?_⟩
  rw [hyd]
  linarith

theorem exists_uniform_physical_annular_root {B C : ℝ} (hB : 0 ≤ B) (hgap : 1 < C - B) :
    ∃ ρ q : ℝ, 0 < ρ ∧ ρ < 1 ∧ 0 < q ∧ q < 1 ∧
      ∀ y : ℂ, ρ ≤ ‖y‖ → ‖y‖ ≤ 1 →
        1 < (physicalAnnularW B C y).re ∧
        AnalyticAt ℂ (physicalAnnularRoot B C) y ∧
        physicalAnnularRoot B C y ≠ 0 ∧ ‖physicalAnnularRoot B C y‖ < q := by
  let K : Set ℂ := sphere 0 1
  have hcont : ContinuousOn (fun y => ‖physicalAnnularRoot B C y‖) K := by
    intro y hy
    have hyn : ‖y‖ = 1 := by simpa only [K, mem_sphere, dist_zero_right] using hy
    exact (physicalAnnularRoot_analyticAt
      (norm_ne_zero_iff.mp (by rw [hyn]; norm_num))
      (physicalAnnularW_unit_gt_one hB hgap hyn)).continuousAt.norm.continuousWithinAt
  obtain ⟨y₀, hy₀, hmax⟩ := (isCompact_sphere (0 : ℂ) 1).exists_isMaxOn
    (show K.Nonempty from ⟨1, by simp [K]⟩) hcont
  have hy₀n : ‖y₀‖ = 1 := by simpa only [K, mem_sphere, dist_zero_right] using hy₀
  have hM : ‖physicalAnnularRoot B C y₀‖ < 1 :=
    (reciprocalInteriorRoot_spec (physicalAnnularW_unit_gt_one hB hgap hy₀n)).2
  let q := (‖physicalAnnularRoot B C y₀‖ + 1) / 2
  have hq : 0 < q := by dsimp [q]; linarith [norm_nonneg (physicalAnnularRoot B C y₀)]
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hMq : ‖physicalAnnularRoot B C y₀‖ < q := by dsimp [q]; linarith
  let U : Set ℂ := {y | y ≠ 0 ∧ 1 < (physicalAnnularW B C y).re ∧
    ‖physicalAnnularRoot B C y‖ < q}
  have hU : IsOpen U := isOpen_iff_mem_nhds.mpr (by
    intro y hy
    have hWa := physicalAnnularW_analyticAt B C hy.1
    have hRa := physicalAnnularRoot_analyticAt hy.1 hy.2.1
    exact (continuousAt_id.eventually_ne hy.1).and
      (((Complex.continuous_re.continuousAt.comp hWa.continuousAt).eventually
        (Ioi_mem_nhds hy.2.1)).and
        (hRa.continuousAt.norm.eventually (Iio_mem_nhds hy.2.2))))
  have hKU : K ⊆ U := by
    intro y hy
    have hyn : ‖y‖ = 1 := by simpa only [K, mem_sphere, dist_zero_right] using hy
    exact ⟨norm_ne_zero_iff.mp (by rw [hyn]; norm_num),
      physicalAnnularW_unit_gt_one hB hgap hyn, (hmax hy).trans_lt hMq⟩
  obtain ⟨ρ, hρ, hρ1, hρU⟩ := inner_annulus_subset_open_of_unit_sphere hU hKU
  refine ⟨ρ, q, hρ, hρ1, hq, hq1, ?_⟩
  intro y hy hy1
  have h := hρU y hy hy1
  exact ⟨h.2.1, physicalAnnularRoot_analyticAt h.1 h.2.1,
    reciprocalInteriorRoot_ne_zero h.2.1, h.2.2⟩

/-- The original physical contour radius and the genuine root gap are chosen
once, before all particle numbers and both lattice displacement signs. -/
theorem exists_physical_root_contour {lam x : ℝ} (hlam : 0 < lam) (hx : 0 < x)
    (hp : realProduct lam x ≠ 1) :
    ∃ r q : ℝ, ContourAnnulus lam (x : ℂ) r ∧ 0 < q ∧ q < r ∧
      ∀ y : ℂ, r ≤ ‖y‖ → ‖y‖ ≤ 1 →
        AnalyticAt ℂ (physicalAnnularRoot (realB lam x) (realC lam x)) y ∧
        physicalAnnularRoot (realB lam x) (realC lam x) y ≠ 0 ∧
        ‖physicalAnnularRoot (realB lam x) (realC lam x) y‖ < q ∧
        physicalAnnularRoot (realB lam x) (realC lam x) y ^ 2 -
          2 * physicalAnnularW (realB lam x) (realC lam x) y *
            physicalAnnularRoot (realB lam x) (realC lam x) y + 1 = 0 := by
  obtain ⟨ρ, q, hρ, hρ1, hq, hq1, hroot⟩ := exists_uniform_physical_annular_root
    (realB_pos_f002 hlam hx).le (published_real_dispersion_gap_f002 hlam hx hp)
  obtain ⟨r₀, hr₀⟩ := literal_contourAnnulus_exists
    (positive_real_not_mem_spectralSetF002 hlam hx hp)
  let r := max ρ (max r₀ ((q + 1) / 2))
  have hρr : ρ ≤ r := le_max_left _ _
  have hr₀r : r₀ ≤ r := (le_max_left _ _).trans (le_max_right _ _)
  have hqr : q < r := (show q < (q + 1) / 2 by linarith).trans_le
    ((le_max_right _ _).trans (le_max_right _ _))
  have hr1 : r < 1 := max_lt hρ1 (max_lt hr₀.2.1 (by linarith))
  refine ⟨r, q, ⟨hρ.trans_le hρr, hr1, ?_⟩, hq, hqr, ?_⟩
  · intro u v hu hu1 hv hv1
    exact hr₀.2.2 u v (hr₀r.trans hu) hu1 (hr₀r.trans hv) hv1
  · intro y hy hy1
    obtain ⟨hW, ha, hn, hnorm⟩ := hroot y (hρr.trans hy) hy1
    exact ⟨ha, hn, hnorm, (reciprocalInteriorRoot_spec hW).1⟩

end
end IsingBulk.AnisoF002.RegularTail.C03
