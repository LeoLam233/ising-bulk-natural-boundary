import IsingBulk.Anisotropic.FormFactors.AnnularHolomorphy
import IsingBulk.Anisotropic.FormFactors.MixedFubini

namespace IsingBulk.Anisotropic.FormFactors
noncomputable section
open IsingBulk.First Set

theorem fullDensity_mixed_continuous (N : ℕ) (hN : 0 < N) {r R rx ry lam : ℝ} {z : ℂ}
    (h : ContourAnnulus lam z r) (hR : R < 1)
    (hx : r ≤ rx ∧ rx ≤ R) (hy : r ≤ ry ∧ ry ≤ R) :
    Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      fullDensity lam z (angleTuple rx p.1) (angleTuple ry p.2)) := by
  have hmap := ((angleTuple_continuous (N := N) rx).comp continuous_fst).prodMk
    ((angleTuple_continuous (N := N) ry).comp continuous_snd)
  apply continuous_iff_continuousAt.mpr
  intro p
  have hpx : angleTuple rx p.1 ∈ annularProduct N r R := by
    intro i
    change r ≤ ‖anglePoint rx (p.1 i)‖ ∧ ‖anglePoint rx (p.1 i)‖ ≤ R
    rw [anglePoint_norm (h.1.trans_le hx.1).le]
    exact hx
  have hpy : angleTuple ry p.2 ∈ annularProduct N r R := by
    intro i
    change r ≤ ‖anglePoint ry (p.2 i)‖ ∧ ‖anglePoint ry (p.2 i)‖ ≤ R
    rw [anglePoint_norm (h.1.trans_le hy.1).le]
    exact hy
  have hd := fullDensity_differentiableAt_maps hN h hR
    (Prod.fst : (Fin N → ℂ) × (Fin N → ℂ) → (Fin N → ℂ)) Prod.snd
    (angleTuple rx p.1,angleTuple ry p.2) differentiableAt_fst differentiableAt_snd hpx hpy
  have hc : ContinuousAt (fun q : (Fin N → ℝ) × (Fin N → ℝ) =>
      (angleTuple rx q.1,angleTuple ry q.2)) p := hmap.continuousAt
  convert! hd.continuousAt.comp_of_eq hc rfl using 1

theorem fullContour_x_radius_eq (N : ℕ) (hN : 0 < N) {r R ry lam : ℝ} {z : ℂ}
    (h : ContourAnnulus lam z r) (hR : R < 1) (hrR : r ≤ R) (hy : r ≤ ry ∧ ry ≤ R) :
    multiCircleIntegral ry N (fun y => multiCircleIntegral R N (fun x => fullDensity lam z x y)) =
    multiCircleIntegral ry N (fun y => multiCircleIntegral r N (fun x => fullDensity lam z x y)) := by
  apply multiCircleIntegral_congr (h.1.trans_le hy.1).le N
  intro y hyc
  have hyb : y ∈ annularProduct N r R := fun i => by rw [hyc i]; exact hy
  apply multiCircleIntegral_radius_eq N h.1 hrR
  intro x hx
  exact fullDensity_differentiableAt_maps hN h hR id (fun _ => y) x
    differentiableAt_id (differentiableAt_const y) hx hyb

theorem fullContour_y_radius_eq (N : ℕ) (hN : 0 < N) {r R rx lam : ℝ} {z : ℂ}
    (h : ContourAnnulus lam z r) (hR : R < 1) (hrR : r ≤ R) (hx : r ≤ rx ∧ rx ≤ R) :
    multiCircleIntegral rx N (fun x => multiCircleIntegral R N (fun y => fullDensity lam z x y)) =
    multiCircleIntegral rx N (fun x => multiCircleIntegral r N (fun y => fullDensity lam z x y)) := by
  apply multiCircleIntegral_congr (h.1.trans_le hx.1).le N
  intro x hxc
  have hxb : x ∈ annularProduct N r R := fun i => by rw [hxc i]; exact hx
  apply multiCircleIntegral_radius_eq N h.1 hrR
  intro y hy
  exact fullDensity_differentiableAt_maps hN h hR (fun _ => x) id y
    (differentiableAt_const x) differentiableAt_id hxb hy

/-- Both contour groups move through a proved zero-free annulus. Fubini is
needed because anisotropic x/y exchange is not a symmetry of the density. -/
theorem unscaledFullCoefficientAtRadius_eq (N : ℕ) (hN : 0 < N) {r R lam : ℝ} {z : ℂ}
    (h : ContourAnnulus lam z r) (hR : R < 1) (hrR : r ≤ R) :
    unscaledFullCoefficientAtRadius N R lam z = unscaledFullCoefficientAtRadius N r lam z := by
  unfold unscaledFullCoefficientAtRadius
  congr 1
  rw [fullContour_x_radius_eq N hN h hR hrR ⟨hrR,le_rfl⟩]
  rw [mixedDoubleContour_swap N r R _
    (fullDensity_mixed_continuous N hN h hR ⟨le_rfl,hrR⟩ ⟨hrR,le_rfl⟩)]
  rw [fullContour_y_radius_eq N hN h hR hrR ⟨le_rfl,hrR⟩]
  exact (mixedDoubleContour_swap N r r _
    (fullDensity_mixed_continuous N hN h hR ⟨le_rfl,hrR⟩ ⟨le_rfl,hrR⟩)).symm

theorem unscaledFullCoefficient_radius_independent (N : ℕ) (hN : 0 < N)
    {r R lam : ℝ} {z : ℂ} (hr : ContourAnnulus lam z r) (hR : ContourAnnulus lam z R) :
    unscaledFullCoefficientAtRadius N r lam z = unscaledFullCoefficientAtRadius N R lam z := by
  rcases le_total r R with h | h
  · exact (unscaledFullCoefficientAtRadius_eq N hN hr hR.2.1 h).symm
  · exact unscaledFullCoefficientAtRadius_eq N hN hR hr.2.1 h

theorem unscaledFullCoefficient_eq_fixed_radius (N : ℕ) (hN : 0 < N)
    {r lam : ℝ} {z : ℂ} (hz : z ∉ spectralSet lam) (hr : ContourAnnulus lam z r) :
    unscaledFullCoefficient N lam z = unscaledFullCoefficientAtRadius N r lam z :=
  unscaledFullCoefficient_radius_independent N hN (contourRadius_valid hz) hr
end
end IsingBulk.Anisotropic.FormFactors
