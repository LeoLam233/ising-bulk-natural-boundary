import IsingBulk.Anisotropic.FormFactors.ComplexContours
import Mathlib.Topology.MetricSpace.Thickening
import IsingBulk.Anisotropic.Geometry.Torus

namespace IsingBulk.Anisotropic.FormFactors
noncomputable section
open Set Metric

/-- Radial projection onto the unit circle has exactly its radial distance. -/
theorem unit_projection {x : ℂ} (hx : x ≠ 0) (hx1 : ‖x‖ ≤ 1) :
    ‖(‖x‖:ℂ)⁻¹*x‖ = 1 ∧ dist x ((‖x‖:ℂ)⁻¹*x) = 1-‖x‖ := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hn0 : (‖x‖:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hn.ne'
  constructor
  · rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hn]
    exact inv_mul_cancel₀ hn.ne'
  · rw [dist_eq_norm]
    have he : x-(‖x‖:ℂ)⁻¹*x = ((1-‖x‖⁻¹:ℝ):ℂ)*x := by push_cast; ring
    rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos]
    · field_simp
      ring
    · have hi : 1 ≤ ‖x‖⁻¹ := (one_le_inv₀ hn).mpr hx1
      linarith

/-- A compact zero-free unit torus has a zero-free inner product annulus.
This is a geometric compactness theorem independent of susceptibility. -/
theorem exists_inner_annulus (F : ℂ × ℂ → ℂ)
    (hc : ∀ p : ℂ × ℂ, p.1 ≠ 0 → p.2 ≠ 0 → ContinuousAt F p)
    (hF : ∀ x y : ℂ, ‖x‖ = 1 → ‖y‖ = 1 → F (x,y) ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ x y : ℂ,
      r ≤ ‖x‖ → ‖x‖ ≤ 1 → r ≤ ‖y‖ → ‖y‖ ≤ 1 → F (x,y) ≠ 0 := by
  let K : Set (ℂ × ℂ) := sphere (0:ℂ) 1 ×ˢ sphere (0:ℂ) 1
  let U : Set (ℂ × ℂ) := {p | p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ F p ≠ 0}
  have hK : IsCompact K := (isCompact_sphere _ _).prod (isCompact_sphere _ _)
  have hU : IsOpen U := isOpen_iff_mem_nhds.mpr (by
    intro p hp
    exact (continuousAt_fst.eventually_ne hp.1).and
      ((continuousAt_snd.eventually_ne hp.2.1).and ((hc p hp.1 hp.2.1).eventually_ne hp.2.2)))
  have hKU : K ⊆ U := by
    rintro ⟨x,y⟩ ⟨hx,hy⟩
    have hx' : ‖x‖ = 1 := by simpa using hx
    have hy' : ‖y‖ = 1 := by simpa using hy
    exact ⟨norm_ne_zero_iff.mp (by rw [hx']; norm_num),
      norm_ne_zero_iff.mp (by rw [hy']; norm_num), hF x y hx' hy'⟩
  obtain ⟨d,hd,hsub⟩ := hK.exists_thickening_subset_open hU hKU
  let e := min (d/2) (1/2:ℝ)
  have he : 0 < e := lt_min (by positivity) (by norm_num)
  have he1 : e ≤ 1/2 := min_le_right _ _
  have hed : e < d := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  refine ⟨1-e,by linarith,by linarith,?_⟩
  intro x y hx hx1 hy hy1
  have hx0 : x ≠ 0 := norm_pos_iff.mp (by linarith)
  have hy0 : y ≠ 0 := norm_pos_iff.mp (by linarith)
  obtain ⟨hxn,hxd⟩ := unit_projection hx0 hx1
  obtain ⟨hyn,hyd⟩ := unit_projection hy0 hy1
  have hm : (x,y) ∈ thickening d K := by
    rw [mem_thickening_iff]
    refine ⟨((‖x‖:ℂ)⁻¹*x,(‖y‖:ℂ)⁻¹*y),?_,?_⟩
    · exact ⟨by simpa using hxn,by simpa using hyn⟩
    · rw [Prod.dist_eq,max_lt_iff]
      constructor
      · change dist x ((‖x‖:ℂ)⁻¹*x) < d
        rw [hxd]; linarith
      · change dist y ((‖y‖:ℂ)⁻¹*y) < d
        rw [hyd]; linarith
  exact (hsub hm).2.2
/-- The radius used by the actual full contours exists at every point of
 the independently defined spectral complement. -/
theorem contourAnnulus_exists {lam : ℝ} {z : ℂ} (hz : z ∉ spectralSet lam) :
    ∃ r, ContourAnnulus lam z r := by
  apply exists_inner_annulus (fun p => sliceDispersion lam z p.1 p.2)
  · intro p hp1 hp2
    unfold sliceDispersion dispersionPolynomial
    exact (continuousAt_const.sub
      (continuousAt_const.mul (continuousAt_fst.add (continuousAt_fst.inv₀ hp1)))).sub
      (continuousAt_const.mul (continuousAt_snd.add (continuousAt_snd.inv₀ hp2)))
  · intro x y hx hy
    exact torus_polynomial_ne_zero hz hx hy

theorem contourRadius_valid {lam : ℝ} {z : ℂ} (hz : z ∉ spectralSet lam) :
    ContourAnnulus lam z (contourRadius lam z) :=
  contourRadius_spec (contourAnnulus_exists hz)
end
end IsingBulk.Anisotropic.FormFactors
