import IsingBulk.HT22.Tail.KernelAnalytic
import IsingBulk.HT22.Tail.MarkedTransport

/-! The actual physical domain supplies the complex parameter and real
angular differentiability needed by ordinary marked transport. -/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Geometry
open scoped BigOperators Topology Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

/-- Parameter analyticity of the actual unshifted forward coordinate. -/
theorem sourceCoordinate_parameter_analyticAt {N : ℕ}
    (τ : ℝ) (p m : ℝ → ℝ) (t : ℂ) (θ : Fin N → ℝ)
    (ht : t≠0)
    (hW : ∀ i, 0<(temperatureTrace t-Complex.cos (deformedAngles τ p m θ i)).im) :
    AnalyticAt ℂ (fun s => sourceCoordinate τ p m s θ) t := by
  have hS : AnalyticAt ℂ temperatureTrace t := analyticAt_id.add (analyticAt_id.inv ht)
  apply AnalyticAt.pi
  intro i
  have hφ : AnalyticAt ℂ (fun s => physicalPhase s (deformedAngles τ p m θ i)) t :=
    AnalyticAt.comp (f := fun s : ℂ => temperatureTrace s-Complex.cos (deformedAngles τ p m θ i))
      (g := preferredArccos) (IsingBulk.Branch.lowerArccos_analytic_of_upper (hW i))
      (hS.sub analyticAt_const)
  exact analyticAt_const.add hφ

/-- The source angular map differentiates the real bumps directly. -/
theorem sourceCoordinate_angular_differentiable {N : ℕ}
    (τ : ℝ) (p m : ℝ → ℝ) (hp : Differentiable ℝ p) (hm : Differentiable ℝ m)
    (t : ℂ) (θ : Fin N → ℝ)
    (hW : ∀ i, 0<(temperatureTrace t-Complex.cos (deformedAngles τ p m θ i)).im)
    (j : Fin N) :
    DifferentiableAt ℝ (fun x => sourceCoordinate τ p m t (Function.update θ j x)) (θ j) := by
  apply differentiableAt_pi.mpr
  intro i
  have hwa : AnalyticAt ℂ (sumCoordinate t) (deformedAngles τ p m θ i) :=
    analyticAt_id.add (AnalyticAt.comp
      (f := fun w : ℂ => temperatureTrace t-Complex.cos w) (g := preferredArccos)
      (IsingBulk.Branch.lowerArccos_analytic_of_upper (hW i))
      (analyticAt_const.sub Complex.analyticAt_cos))
  have hd := (hwa.differentiableAt.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt_of_eq (θ j)
    (preferred_deformedAngle_hasDerivAt τ p m hp hm θ i j)
    (by simp only [Function.update_eq_self])
  exact hd.differentiableAt

/-- Both calculus premises of the sharp ordinary-marked recursion are
proved from primitive contour margins and differentiable real bumps. -/
theorem sourceOrdinaryKernel_differentiable {N : ℕ}
    (τ δ : ℝ) (p m : ℝ → ℝ) (hp : Differentiable ℝ p) (hm : Differentiable ℝ m)
    (t : ℂ) (θ : Fin N → ℝ)
    (hδ : 0<δ) (hδπ : δ<Real.pi/2)
    (hS : 0<(temperatureTrace t).re) (hSδ : (temperatureTrace t).re<2*Real.cos δ)
    (hθ : ∀ i, θ i∈Set.Icc (-Real.pi-δ) δ)
    (hW : ∀ i, 0<(temperatureTrace t-Complex.cos (deformedAngles τ p m θ i)).im) :
    DifferentiableAt ℂ (fun s => sourceOrdinaryKernel τ p m s θ) t ∧
      ∀ j, DifferentiableAt ℝ
        (fun x => sourceOrdinaryKernel τ p m t (Function.update θ j x)) (θ j) := by
  have ht : t≠0 := by intro hz; simp [hz,temperatureTrace] at hS
  have hK := source_regularOrdinaryKernel_analyticAt τ δ p m t θ hδ hδπ hS hSδ hθ hW
  have hχ := sourceCoordinate_parameter_analyticAt τ p m t θ ht hW
  constructor
  · exact hK.differentiableAt.comp t (differentiableAt_id.prodMk hχ.differentiableAt)
  · intro j
    have hcoord := sourceCoordinate_angular_differentiable τ p m hp hm t θ hW j
    have hkreal : DifferentiableAt ℝ
        (fun z : ℂ × (Fin N → ℂ) => regularOrdinaryKernel z.1 z.2)
        (t,sourceCoordinate τ p m t (Function.update θ j (θ j))) := by
      simpa only [Function.update_eq_self] using hK.differentiableAt.restrictScalars ℝ
    exact DifferentiableAt.comp
      (f := fun x : ℝ => (t,sourceCoordinate τ p m t (Function.update θ j x)))
      (g := fun z : ℂ × (Fin N → ℂ) => regularOrdinaryKernel z.1 z.2)
      (θ j) hkreal ((differentiableAt_const t).prodMk hcoord)

end
end IsingBulk.HT22.Tail
