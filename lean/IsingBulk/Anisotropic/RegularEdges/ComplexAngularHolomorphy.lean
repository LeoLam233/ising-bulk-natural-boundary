import IsingBulk.Anisotropic.RegularEdges.ComplexAngular
import IsingBulk.Anisotropic.Geometry.ClosedSpectralSet
import IsingBulk.First.CompactIntegralHolomorphic
import IsingBulk.First.AngularFubini
import IsingBulk.HT.Contour.PhysicalAngularRegularity

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.HT.Contour Set Filter MeasureTheory
open scoped Topology

theorem unscaledAngularCoefficient_analyticAt (n : ℕ) {lam : ℝ} {z : ℂ}
    (hz : z∉spectralSet lam) (hS : spectralS z≠0) :
    AnalyticAt ℂ (unscaledAngularCoefficient n lam) z := by
  let U : Set ℂ := (spectralSet lam)ᶜ ∩ {w | spectralS w≠0}
  have hU : IsOpen U := (spectralSet_isClosed lam).isOpen_compl.inter
    (isOpen_ne_fun Complex.continuous_sinh continuous_const)
  let psi : (Fin n → ℝ) → (Fin (n+1) → ℂ) :=
    fun q i => (physicalDependentAngles n q i:ℂ)
  have hpsi : Continuous psi := continuous_pi (fun i => Complex.continuous_ofReal.comp
    ((continuous_apply i).comp (physicalDependentAngles_continuous n)))
  let F : ℂ × (Fin (n+1) → ℂ) → ℂ := fun p => complexAngularDensity lam p.1 p.2
  have hF : ∀ w∈U, ∀ q∈angleBox n, AnalyticAt ℂ F (w,psi q) := by
    intro w hw q _
    exact complexAngularDensity_joint_analyticAt (by omega) hw.1 hw.2 (physicalDependentAngles n q)
  have hcont (w : ℂ) (hw : w∈U) : Continuous (fun q => F (w,psi q)) := by
    apply continuous_iff_continuousAt.mpr
    intro q
    exact (complexAngularDensity_joint_analyticAt (by omega) hw.1 hw.2
      (physicalDependentAngles n q)).continuousAt.comp
      (f := fun q => (w,psi q)) (continuous_const.prodMk hpsi).continuousAt
  have ha := compact_analytic_shape_integral_analyticAt
    (μ := volume) (K := angleBox n) isCompact_Icc hU F psi hpsi
    (fun _ => (1:ℂ)) continuous_const hF (show z∈U from ⟨hz,hS⟩)
  have hb : AnalyticAt ℂ (fun w => multiAngleIntegral n (fun q => F (w,psi q))) z := by
    apply ha.congr
    filter_upwards [hU.mem_nhds (show z∈U from ⟨hz,hS⟩)] with w hw
    simpa only [one_mul] using (multiAngleIntegral_eq_box n (fun q => F (w,psi q)) (hcont w hw)).symm
  exact analyticAt_const.mul hb

end
end IsingBulk.Anisotropic.RegularEdges
