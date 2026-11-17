import IsingBulk.AnisoF002.Geometry.CanonicalRootContinuity
import IsingBulk.Anisotropic.FormFactors.ComplexContours
import Mathlib.Topology.MetricSpace.Thickening

/-!
# The literal full-contour annulus from the independent F002 spectrum

The zero-free annulus and its parameter neighborhood are constructed
from compactness of the actual unit torus.  This establishes that the
radius selected in the unchanged target definitions is genuinely
admissible.  No historical contour-annulus theorem is invoked.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set Filter Metric IsingBulk.Anisotropic IsingBulk.Anisotropic.FormFactors
  IsingBulk.AnisoF002.Geometry
open scoped Topology

theorem literal_unit_trace (x : ℂ) (hx : ‖x‖ = 1) : x + x⁻¹ = 2 * (x.re : ℂ) := by
  rw [Complex.inv_eq_conj hx]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.conj_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    norm_num
    ring
  · simp

theorem literal_torus_dispersion_ne_zero {lam : ℝ} {z : ℂ}
    (hz : z ∉ spectralSetF002 lam) {x y : ℂ} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    sliceDispersion lam z x y ≠ 0 := by
  intro he
  apply hz
  have hxr : x.re ∈ Icc (-1 : ℝ) 1 := by
    have h := Complex.abs_re_le_norm x
    simpa only [hx, abs_le, Set.mem_Icc] using h
  have hyr : y.re ∈ Icc (-1 : ℝ) 1 := by
    have h := Complex.abs_re_le_norm y
    simpa only [hy, abs_le, Set.mem_Icc] using h
  refine ⟨x.re, hxr, y.re, hyr, ?_⟩
  change spectralA lam z - spectralS z / 2 * (x + x⁻¹) -
    spectralT lam z / 2 * (y + y⁻¹) = 0 at he
  rw [literal_unit_trace x hx, literal_unit_trace y hy] at he
  linear_combination he

theorem radial_projection_distance {x : ℂ} (hx : x ≠ 0) (hx1 : ‖x‖ ≤ 1) :
    ‖(‖x‖ : ℂ)⁻¹ * x‖ = 1 ∧ dist x ((‖x‖ : ℂ)⁻¹ * x) = 1 - ‖x‖ := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  constructor
  · rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hn.le,
      inv_mul_cancel₀ hn.ne']
  · rw [dist_eq_norm]
    have he : x - (‖x‖ : ℂ)⁻¹ * x = ((1 - ‖x‖⁻¹ : ℝ) : ℂ) * x := by push_cast; ring
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by have h := (one_le_inv₀ hn).mpr hx1; linarith)]
    field_simp
    ring

theorem inner_annulus_of_torus_gap (F : ℂ × ℂ → ℂ)
    (hc : ∀ p, p.1 ≠ 0 → p.2 ≠ 0 → ContinuousAt F p)
    (hF : ∀ x y : ℂ, ‖x‖ = 1 → ‖y‖ = 1 → F (x, y) ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ x y : ℂ,
      r ≤ ‖x‖ → ‖x‖ ≤ 1 → r ≤ ‖y‖ → ‖y‖ ≤ 1 → F (x, y) ≠ 0 := by
  let K : Set (ℂ × ℂ) := sphere (0 : ℂ) 1 ×ˢ sphere (0 : ℂ) 1
  let U : Set (ℂ × ℂ) := {p | p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ F p ≠ 0}
  have hK : IsCompact K := (isCompact_sphere _ _).prod (isCompact_sphere _ _)
  have hU : IsOpen U := isOpen_iff_mem_nhds.mpr (by
    intro p hp
    exact (continuousAt_fst.eventually_ne hp.1).and
      ((continuousAt_snd.eventually_ne hp.2.1).and ((hc p hp.1 hp.2.1).eventually_ne hp.2.2)))
  have hKU : K ⊆ U := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    have hx' : ‖x‖ = 1 := by simpa using hx
    have hy' : ‖y‖ = 1 := by simpa using hy
    exact ⟨norm_ne_zero_iff.mp (by rw [hx']; norm_num),
      norm_ne_zero_iff.mp (by rw [hy']; norm_num), hF x y hx' hy'⟩
  obtain ⟨delta, hd, hsub⟩ := hK.exists_thickening_subset_open hU hKU
  let e := min (delta / 2) (1 / 2 : ℝ)
  have he : 0 < e := lt_min (half_pos hd) (by norm_num)
  have he1 : e ≤ 1 / 2 := min_le_right _ _
  have hed : e < delta := (min_le_left _ _).trans_lt (half_lt_self hd)
  refine ⟨1 - e, by linarith, by linarith, ?_⟩
  intro x y hx hx1 hy hy1
  have hx0 : x ≠ 0 := norm_pos_iff.mp (by linarith)
  have hy0 : y ≠ 0 := norm_pos_iff.mp (by linarith)
  obtain ⟨hxn, hxd⟩ := radial_projection_distance hx0 hx1
  obtain ⟨hyn, hyd⟩ := radial_projection_distance hy0 hy1
  have hm : (x, y) ∈ thickening delta K := by
    rw [mem_thickening_iff]
    refine ⟨((‖x‖ : ℂ)⁻¹ * x, (‖y‖ : ℂ)⁻¹ * y),
      ⟨by simpa using hxn, by simpa using hyn⟩, ?_⟩
    rw [Prod.dist_eq, max_lt_iff]
    constructor
    · change dist x ((‖x‖ : ℂ)⁻¹ * x) < delta
      rw [hxd]
      linarith
    · change dist y ((‖y‖ : ℂ)⁻¹ * y) < delta
      rw [hyd]
      linarith
  exact (hsub hm).2.2

theorem literal_sliceDispersion_continuousAt {lam : ℝ} {z x y : ℂ}
    (hx : x ≠ 0) (hy : y ≠ 0) :
    ContinuousAt (fun p : ℂ × (ℂ × ℂ) => sliceDispersion lam p.1 p.2.1 p.2.2) (z, x, y) := by
  have hzz : ContinuousAt (fun p : ℂ × (ℂ × ℂ) => p.1) (z, x, y) := continuousAt_fst
  have hxx : ContinuousAt (fun p : ℂ × (ℂ × ℂ) => p.2.1) (z, x, y) :=
    continuousAt_fst.comp continuousAt_snd
  have hyy : ContinuousAt (fun p : ℂ × (ℂ × ℂ) => p.2.2) (z, x, y) :=
    continuousAt_snd.comp continuousAt_snd
  unfold sliceDispersion dispersionPolynomial spectralA spectralS spectralT
  have hc := Complex.continuous_cosh.continuousAt.comp hzz
  have hcl := Complex.continuous_cosh.continuousAt.comp
    ((continuousAt_const (y := (lam : ℂ))).mul hzz)
  have hs := Complex.continuous_sinh.continuousAt.comp hzz
  have hsl := Complex.continuous_sinh.continuousAt.comp
    ((continuousAt_const (y := (lam : ℂ))).mul hzz)
  exact ((hc.mul hcl).sub ((hs.div_const 2).mul (hxx.add (hxx.inv₀ hx)))).sub
    ((hsl.div_const 2).mul (hyy.add (hyy.inv₀ hy)))

theorem literal_contourAnnulus_exists {lam : ℝ} {z : ℂ}
    (hz : z ∉ spectralSetF002 lam) : ∃ r, ContourAnnulus lam z r := by
  apply inner_annulus_of_torus_gap (fun p => sliceDispersion lam z p.1 p.2)
  · intro p hp1 hp2
    exact (literal_sliceDispersion_continuousAt hp1 hp2).comp
      (f := fun q : ℂ × ℂ => (z, q)) (continuousAt_const.prodMk continuousAt_id)
  · intro x y hx hy
    exact literal_torus_dispersion_ne_zero hz hx hy

theorem literal_contourRadius_valid {lam : ℝ} {z : ℂ}
    (hz : z ∉ spectralSetF002 lam) : ContourAnnulus lam z (contourRadius lam z) := by
  have h := literal_contourAnnulus_exists hz
  simp only [contourRadius, dite_eq_left h]
  exact Classical.choose_spec h

theorem literal_contourAnnulus_eventually {lam r : ℝ} {z : ℂ}
    (h : ContourAnnulus lam z r) : ∀ᶠ w in 𝓝 z, ContourAnnulus lam w r := by
  let K : Set ℂ := closedBall 0 1 \ ball 0 r
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) 1).diff isOpen_ball
  have hm (x : ℂ) : x ∈ K ↔ r ≤ ‖x‖ ∧ ‖x‖ ≤ 1 := by
    simp only [K, Set.mem_sdiff, mem_closedBall, mem_ball, dist_zero_right, not_lt]
    exact and_comm
  have he : ∀ᶠ w in 𝓝 z, ∀ p ∈ K ×ˢ K, sliceDispersion lam w p.1 p.2 ≠ 0 := by
    apply (hK.prod hK).eventually_forall_of_forall_eventually
    intro p hp
    have hx := (hm p.1).mp hp.1
    have hy := (hm p.2).mp hp.2
    exact (literal_sliceDispersion_continuousAt
      (norm_pos_iff.mp (h.1.trans_le hx.1))
      (norm_pos_iff.mp (h.1.trans_le hy.1))).eventually_ne (h.2.2 _ _ hx.1 hx.2 hy.1 hy.2)
  filter_upwards [he] with w hw
  refine ⟨h.1, h.2.1, ?_⟩
  intro x y hx hx1 hy hy1
  exact hw (x, y) ⟨(hm x).mpr ⟨hx, hx1⟩, (hm y).mpr ⟨hy, hy1⟩⟩

end
end IsingBulk.AnisoF002.RegularTail.C03
