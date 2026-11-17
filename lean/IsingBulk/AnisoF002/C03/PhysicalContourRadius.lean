import IsingBulk.AnisoF002.C03.PhysicalContourIntegration
import IsingBulk.AnisoF002.Geometry.EndpointBoundary
import IsingBulk.First.AnnulusProduct

/-!
# Radius independence of the original anisotropic full coefficients

Each coordinate group moves through its actual zero-free annulus.  F002's
proved mixed-radius Fubini identity is used between the two moves; no
axis-exchange symmetry of anisotropic dispersion is assumed.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set Filter IsingBulk.First IsingBulk.Anisotropic
  IsingBulk.Anisotropic.FormFactors IsingBulk.AnisoF002.Geometry
open scoped Topology

theorem literal_fullContour_x_radius_eq {N : ℕ} (hN : 0 < N)
    {r R ry lam : ℝ} {z : ℂ} (h : ContourAnnulus lam z r)
    (hR : R < 1) (hrR : r ≤ R) (hy : r ≤ ry ∧ ry ≤ R) :
    multiCircleIntegral ry N (fun y => multiCircleIntegral R N (fun x => fullDensity lam z x y)) =
      multiCircleIntegral ry N (fun y => multiCircleIntegral r N (fun x => fullDensity lam z x y)) := by
  apply multiCircleIntegral_congr (h.1.trans_le hy.1).le N
  intro y hyc
  apply multiCircleIntegral_radius_eq N h.1 hrR
  intro x hx
  have ha := literal_fullDensity_joint_analyticAt hN h
    (fun i => ⟨(hx i).1, (hx i).2.trans_lt hR⟩)
    (fun i => ⟨by rw [hyc i]; exact hy.1, by rw [hyc i]; exact hy.2.trans_lt hR⟩)
  exact (ha.comp (f := fun q : Fin N → ℂ => (z, q, y))
    (analyticAt_const.prod (analyticAt_id.prod analyticAt_const))).differentiableAt

theorem literal_fullContour_y_radius_eq {N : ℕ} (hN : 0 < N)
    {r R rx lam : ℝ} {z : ℂ} (h : ContourAnnulus lam z r)
    (hR : R < 1) (hrR : r ≤ R) (hx : r ≤ rx ∧ rx ≤ R) :
    multiCircleIntegral rx N (fun x => multiCircleIntegral R N (fun y => fullDensity lam z x y)) =
      multiCircleIntegral rx N (fun x => multiCircleIntegral r N (fun y => fullDensity lam z x y)) := by
  apply multiCircleIntegral_congr (h.1.trans_le hx.1).le N
  intro x hxc
  apply multiCircleIntegral_radius_eq N h.1 hrR
  intro y hy
  have ha := literal_fullDensity_joint_analyticAt hN h
    (fun i => ⟨by rw [hxc i]; exact hx.1, by rw [hxc i]; exact hx.2.trans_lt hR⟩)
    (fun i => ⟨(hy i).1, (hy i).2.trans_lt hR⟩)
  exact (ha.comp (f := fun q : Fin N → ℂ => (z, x, q))
    (analyticAt_const.prod (analyticAt_const.prod analyticAt_id))).differentiableAt

theorem literal_fixedCoefficient_radius_eq {N : ℕ} (hN : 0 < N)
    {r R lam : ℝ} {z : ℂ} (h : ContourAnnulus lam z r)
    (hR : R < 1) (hrR : r ≤ R) :
    unscaledFullCoefficientAtRadius N R lam z = unscaledFullCoefficientAtRadius N r lam z := by
  unfold unscaledFullCoefficientAtRadius
  congr 1
  rw [literal_fullContour_x_radius_eq hN h hR hrR ⟨hrR, le_rfl⟩]
  rw [literal_doubleContour_swap r R _
    (literal_fullDensity_continuous_angles hN h ⟨le_rfl, h.2.1⟩ ⟨hrR, hR⟩)]
  rw [literal_fullContour_y_radius_eq hN h hR hrR ⟨le_rfl, hrR⟩]
  exact (literal_doubleContour_swap r r _
    (literal_fullDensity_continuous_angles hN h ⟨le_rfl, h.2.1⟩ ⟨le_rfl, h.2.1⟩)).symm

theorem literal_fixedCoefficient_radius_independent {N : ℕ} (hN : 0 < N)
    {r R lam : ℝ} {z : ℂ} (hr : ContourAnnulus lam z r) (hR : ContourAnnulus lam z R) :
    unscaledFullCoefficientAtRadius N r lam z = unscaledFullCoefficientAtRadius N R lam z := by
  rcases le_total r R with hh | hh
  · exact (literal_fixedCoefficient_radius_eq hN hr hR.2.1 hh).symm
  · exact literal_fixedCoefficient_radius_eq hN hR hr.2.1 hh

theorem literal_chosenCoefficient_eq_fixed {N : ℕ} (hN : 0 < N)
    {lam r : ℝ} {z : ℂ} (hz : z ∉ spectralSetF002 lam) (hr : ContourAnnulus lam z r) :
    unscaledFullCoefficient N lam z = unscaledFullCoefficientAtRadius N r lam z :=
  literal_fixedCoefficient_radius_independent hN (literal_contourRadius_valid hz) hr

theorem literal_coefficient_analyticOnNhd (N : ℕ) (hN : 0 < N) (lam : ℝ) :
    AnalyticOnNhd ℂ (unscaledFullCoefficient N lam) (spectralSetF002 lam)ᶜ := by
  intro z hz
  have h := literal_contourRadius_valid hz
  apply (literal_fixedCoefficient_analyticAt hN h).congr
  filter_upwards [literal_contourAnnulus_eventually h,
    (isClosed_spectralSetF002 lam).isOpen_compl.mem_nhds hz] with w hw hwc
  exact (literal_chosenCoefficient_eq_fixed hN hwc hw).symm

end
end IsingBulk.AnisoF002.RegularTail.C03
