import IsingBulk.Anisotropic.FormFactors.JointAnalytic
import IsingBulk.Anisotropic.FormFactors.LocalAnnulus
import IsingBulk.Anisotropic.FormFactors.RadiusIndependence
import IsingBulk.Anisotropic.FormFactors.ContourContinuity
import IsingBulk.Anisotropic.Geometry.ClosedSpectralSet
import IsingBulk.First.CompactIntegralHolomorphic

namespace IsingBulk.Anisotropic.FormFactors
noncomputable section
open IsingBulk.First Set Filter MeasureTheory
open scoped Topology

theorem unscaledFullCoefficientAtRadius_analyticAt (N : ℕ) (hN : 0 < N)
    {lam r : ℝ} {z : ℂ} (h : ContourAnnulus lam z r) :
    AnalyticAt ℂ (unscaledFullCoefficientAtRadius N r lam) z := by
  obtain ⟨U,hUsub,hU,hzU⟩ := mem_nhds_iff.mp (contourAnnulus_eventually h)
  let F := fun p : ℂ × ((Fin N → ℂ) × (Fin N → ℂ)) => fullDensity lam p.1 p.2.1 p.2.2
  let psi := fun p : (Fin N → ℝ) × (Fin N → ℝ) => (angleTuple r p.1,angleTuple r p.2)
  let chi := fun p : (Fin N → ℝ) × (Fin N → ℝ) => angleProductJacobian r p.2*angleProductJacobian r p.1
  have hpsi : Continuous psi := ((angleTuple_continuous r).comp continuous_fst).prodMk
    ((angleTuple_continuous r).comp continuous_snd)
  have hchi : Continuous chi := ((angleProductJacobian_continuous r).comp continuous_snd).mul
    ((angleProductJacobian_continuous r).comp continuous_fst)
  have hF (w : ℂ) (hw : w ∈ U) (q : (Fin N → ℝ) × (Fin N → ℝ))
      (_hq : q ∈ angleBox N ×ˢ angleBox N) : AnalyticAt ℂ F (w,psi q) := by
    apply fullDensity_joint_analyticAt N hN (hUsub hw)
    · intro i
      change r ≤ ‖anglePoint r (q.1 i)‖ ∧ ‖anglePoint r (q.1 i)‖ < 1
      rw [anglePoint_norm h.1.le]
      exact ⟨le_rfl,h.2.1⟩
    · intro i
      change r ≤ ‖anglePoint r (q.2 i)‖ ∧ ‖anglePoint r (q.2 i)‖ < 1
      rw [anglePoint_norm h.1.le]
      exact ⟨le_rfl,h.2.1⟩
  have ha := (analyticAt_const (v := (N.factorial:ℂ)⁻¹)).mul
    (compact_analytic_shape_integral_analyticAt (μ := volume)
      (isCompact_Icc.prod isCompact_Icc) hU F psi hpsi chi hchi hF hzU)
  apply ha.congr
  filter_upwards [hU.mem_nhds hzU] with w hw
  exact (unscaledFullCoefficientAtRadius_eq_box N hN (hUsub hw)).symm

/-- Finite-particle holomorphy of the actual chosen-radius full contour on
 the entire independently defined spectral complement. -/
theorem unscaledFullCoefficient_analyticOnNhd (N : ℕ) (hN : 0 < N) (lam : ℝ) :
    AnalyticOnNhd ℂ (unscaledFullCoefficient N lam) (spectralSet lam)ᶜ := by
  intro z hz
  let r := contourRadius lam z
  have h : ContourAnnulus lam z r := contourRadius_valid hz
  apply (unscaledFullCoefficientAtRadius_analyticAt N hN h).congr
  filter_upwards [contourAnnulus_eventually h,
    (spectralSet_isClosed lam).isOpen_compl.mem_nhds hz] with w hw hwc
  exact (unscaledFullCoefficient_eq_fixed_radius N hN hwc hw).symm
end
end IsingBulk.Anisotropic.FormFactors
