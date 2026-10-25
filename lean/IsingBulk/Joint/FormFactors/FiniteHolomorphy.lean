import IsingBulk.Joint.FormFactors.JointAnalytic
import IsingBulk.Joint.FormFactors.LocalAnnulus
import IsingBulk.Joint.FormFactors.RadiusIndependence
import IsingBulk.Joint.FormFactors.ContourContinuity
import IsingBulk.Joint.Geometry.Basic
import IsingBulk.Joint.FormFactors.CompactIntegral

namespace IsingBulk.Joint.FormFactors
noncomputable section
open IsingBulk.First Set Filter MeasureTheory
open scoped Topology

theorem unscaledFullCoefficientAtRadius_contDiffAt (j N : ℕ) (hN : 0 < N)
    {r : ℝ} {z : Coupling} (h : ContourAnnulus z r) :
    ContDiffAt ℂ j (unscaledFullCoefficientAtRadius N r) z := by
  obtain ⟨U,hUsub,hU,hzU⟩ := mem_nhds_iff.mp (contourAnnulus_eventually h)
  let F := fun p : Coupling × ((Fin N → ℂ) × (Fin N → ℂ)) => fullDensity p.1 p.2.1 p.2.2
  let psi := fun p : (Fin N → ℝ) × (Fin N → ℝ) => (angleTuple r p.1,angleTuple r p.2)
  let chi := fun p : (Fin N → ℝ) × (Fin N → ℝ) => angleProductJacobian r p.2*angleProductJacobian r p.1
  have hpsi : Continuous psi := ((angleTuple_continuous r).comp continuous_fst).prodMk
    ((angleTuple_continuous r).comp continuous_snd)
  have hchi : Continuous chi := ((angleProductJacobian_continuous r).comp continuous_snd).mul
    ((angleProductJacobian_continuous r).comp continuous_fst)
  have hF (w : Coupling) (hw : w ∈ U) (q : (Fin N → ℝ) × (Fin N → ℝ))
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
  have ha := (contDiffAt_const (c := (N.factorial:ℂ)⁻¹)).mul
    (compact_analytic_shape_integral_contDiffAt j (μ := volume)
      (isCompact_Icc.prod isCompact_Icc) hU F psi hpsi chi hchi hF hzU)
  apply ha.congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hzU] with w hw
  exact unscaledFullCoefficientAtRadius_eq_box N hN (hUsub hw)


/-- Genuine joint complex Fréchet smoothness, in every finite order, of the
actual chosen-radius full contour on the independent spectral complement. -/
theorem unscaledFullCoefficient_contDiffAt (j N : ℕ) (hN : 0 < N)
    {K : Coupling} (hK : K ∉ spectralSet) :
    ContDiffAt ℂ j (unscaledFullCoefficient N) K := by
  let r := contourRadius K
  have h : ContourAnnulus K r := contourRadius_valid hK
  apply (unscaledFullCoefficientAtRadius_contDiffAt j N hN h).congr_of_eventuallyEq
  filter_upwards [contourAnnulus_eventually h,
    spectralSet_isClosed.isOpen_compl.mem_nhds hK] with L hL hLc
  exact unscaledFullCoefficient_eq_fixed_radius N hN hLc hL

theorem unscaledFullCoefficient_differentiableOn (N : ℕ) (hN : 0 < N) :
    DifferentiableOn ℂ (unscaledFullCoefficient N) spectralSetᶜ := by
  intro K hK
  exact (unscaledFullCoefficient_contDiffAt 1 N hN hK).differentiableAt_one.differentiableWithinAt
end
end IsingBulk.Joint.FormFactors
