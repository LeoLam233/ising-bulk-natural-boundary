import IsingBulk.Joint.Negative.AngularDensity
import IsingBulk.Joint.FormFactors.CompactIntegral
import IsingBulk.Joint.FormFactors.Restriction
import IsingBulk.Joint.Geometry.Basic
import IsingBulk.Anisotropic.RegularEdges.ComplexAngularIdentity

/-! # Joint physical angular coefficients
These are the full-site coefficients with the canonical inside root, before any
edge continuation or selection of a transverse curve.
-/
namespace IsingBulk.Joint.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.HT.Contour Set Filter MeasureTheory
open scoped Topology

theorem physicalAngular_contDiffAt (j n : ℕ) {K : Coupling}
    (hK : K∉spectralSet) (hS : S K≠0) :
    ContDiffAt ℂ j (Negative.unscaledAngularCoefficient n) K := by
  let U : Set Coupling := spectralSetᶜ ∩ {L | S L≠0}
  have hU : IsOpen U := spectralSet_isClosed.isOpen_compl.inter
    (isOpen_ne_fun continuous_S continuous_const)
  let psi : (Fin n → ℝ) → (Fin (n+1) → ℂ) :=
    fun q i => (physicalDependentAngles n q i:ℂ)
  have hpsi : Continuous psi := continuous_pi (fun i => Complex.continuous_ofReal.comp
    ((continuous_apply i).comp (physicalDependentAngles_continuous n)))
  let F : Coupling × (Fin (n+1) → ℂ) → ℂ := fun p => Negative.complexAngularDensity p.1 p.2
  have hF : ∀ L∈U, ∀ q∈angleBox n, AnalyticAt ℂ F (L,psi q) := by
    intro L hL q _
    exact Negative.complexAngularDensity_joint_analyticAt (by omega) hL.1 hL.2 (physicalDependentAngles n q)
  have hcont (L : Coupling) (hL : L∈U) : Continuous (fun q => F (L,psi q)) := by
    apply continuous_iff_continuousAt.mpr
    intro q
    exact (Negative.complexAngularDensity_joint_analyticAt (by omega) hL.1 hL.2
      (physicalDependentAngles n q)).continuousAt.comp
      (f := fun q => (L,psi q)) (continuous_const.prodMk hpsi).continuousAt
  have ha := FormFactors.compact_analytic_integral_contDiffAt j
    (μ := volume) (K := angleBox n) isCompact_Icc hU F psi hpsi hF
    (show K∈U from ⟨hK,hS⟩)
  have hb : ContDiffAt ℂ j (fun L => multiAngleIntegral n (fun q => F (L,psi q))) K := by
    apply ha.congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds (show K∈U from ⟨hK,hS⟩)] with L hL
    exact multiAngleIntegral_eq_box n (fun q => F (L,psi q)) (hcont L hL)
  exact contDiffAt_const.mul hb

@[simp] theorem physicalAngular_ratioSlice (n : ℕ) (lam : ℝ) (z : ℂ) :
    Negative.unscaledAngularCoefficient n (ratioSlice lam z) =
      Anisotropic.RegularEdges.unscaledAngularCoefficient n lam z := rfl

/-- The real physical identity covers an open two-real-dimensional quadrant,
not just one fixed ratio. The ratio is chosen from each independent pair. -/
theorem fullCoefficient_eq_physicalAngular_real (n : ℕ) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) (hp : Real.sinh x * Real.sinh y ≠ 1)
    (hK : ((x:ℂ),(y:ℂ)) ∉ spectralSet) :
    FormFactors.unscaledFullCoefficient (n+1) ((x:ℂ),(y:ℂ)) =
      Negative.unscaledAngularCoefficient n ((x:ℂ),(y:ℂ)) := by
  let lam := y/x
  have hl : 0 < lam := div_pos hy hx
  have he : ratioSlice lam (x:ℂ) = ((x:ℂ),(y:ℂ)) := by
    apply Prod.ext
    · rfl
    · change ((y/x:ℝ):ℂ)*(x:ℂ)=(y:ℂ)
      exact_mod_cast div_mul_cancel₀ y hx.ne'
  have hp' : Anisotropic.FormFactors.realProduct lam x ≠ 1 := by
    simpa [Anisotropic.FormFactors.realProduct,lam,div_mul_cancel₀ y hx.ne'] using hp
  have hspec : (x:ℂ) ∉ Anisotropic.spectralSet lam := by
    change ratioSlice lam (x:ℂ) ∉ spectralSet
    rwa [he]
  rw [←he,FormFactors.unscaledFullCoefficient_ratioSlice (n+1) (by omega) hspec,
    physicalAngular_ratioSlice]
  exact Anisotropic.RegularEdges.unscaledFullCoefficient_eq_angular_real n hl hx hp'

end
end IsingBulk.Joint.RegularEdges
