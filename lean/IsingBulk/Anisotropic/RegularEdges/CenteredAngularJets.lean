import IsingBulk.Anisotropic.RegularEdges.CenteredAngular
import IsingBulk.Tail.BoundedWeightAnalyticIntegral

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour Set Filter MeasureTheory
open scoped Topology

theorem unscaledAngularCoefficient_comp_iteratedDeriv (n j : ℕ)
    {lam : ℝ} {U : Set ℂ} {zeta : ℂ → ℂ} (hU : IsOpen U)
    (ha : AnalyticOnNhd ℂ zeta U) (hz : ∀ u∈U, zeta u∉spectralSet lam)
    (hS : ∀ u∈U, spectralS (zeta u)≠0) {u : ℂ} (hu : u∈U) :
    iteratedDeriv j (fun v => unscaledAngularCoefficient n lam (zeta v)) u =
      ((n+1).factorial:ℂ)⁻¹*((2*(Real.pi:ℂ))⁻¹)^n *
        ∫ q in Icc (fun _ : Fin n => -Real.pi) (fun _ => Real.pi),
          iteratedDeriv j (fun v => complexAngularDensity lam (zeta v)
            (fun i => (physicalDependentAngles n q i:ℂ))) u := by
  let K : Set (Fin n → ℝ) := Icc (fun _ => -Real.pi) (fun _ => Real.pi)
  let psi : (Fin n → ℝ) → (Fin (n+1) → ℂ) := fun q i => (physicalDependentAngles n q i:ℂ)
  let C : ℂ := ((n+1).factorial:ℂ)⁻¹*((2*(Real.pi:ℂ))⁻¹)^n
  let F : ℂ × (Fin (n+1) → ℂ) → ℂ := fun p => complexAngularDensity lam (zeta p.1) p.2
  have hp : Continuous psi := continuous_pi (fun i => Complex.continuous_ofReal.comp
    ((continuous_apply i).comp (physicalDependentAngles_continuous n)))
  have hF : ∀ v∈U, ∀ q∈K, AnalyticAt ℂ F (v,psi q) := by
    intro v hv q _
    exact AnalyticAt.fun_comp_of_eq
      (f := fun p : ℂ × (Fin (n+1) → ℂ) => (zeta p.1,p.2))
      (g := fun p : ℂ × (Fin (n+1) → ℂ) => complexAngularDensity lam p.1 p.2)
      (complexAngularDensity_joint_analyticAt (by omega) (hz v hv) (hS v hv)
        (physicalDependentAngles n q))
      (((ha v hv).comp (f := fun p : ℂ × (Fin (n+1) → ℂ) => p.1) analyticAt_fst).prod analyticAt_snd) rfl
  have he : (fun v => unscaledAngularCoefficient n lam (zeta v)) =ᶠ[𝓝 u]
      (fun v => ∫ q in K, C*F (v,psi q)) := by
    filter_upwards [hU.mem_nhds hu] with v hv
    rw [unscaledAngularCoefficient_eq_centered n (hz v hv) (hS v hv),integral_const_mul]
  rw [he.iteratedDeriv_eq j]
  have hj := compact_bounded_weight_integral_iteratedDeriv (μ := volume) (K := K)
    isCompact_Icc hU F psi hp hF (fun _ => C) aestronglyMeasurable_const
    (norm_nonneg C) (Filter.Eventually.of_forall (fun _ => le_refl ‖C‖)) j hu
  rw [hj,integral_const_mul]

end
end IsingBulk.Anisotropic.RegularEdges
