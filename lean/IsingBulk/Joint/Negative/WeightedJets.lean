import IsingBulk.Anisotropic.NegativeDominance.WeightedAngularJets
import IsingBulk.Joint.Negative.UpperPeriod
import IsingBulk.Joint.Negative.CanonicalJets

namespace IsingBulk.Joint.Negative
noncomputable section
open IsingBulk.Anisotropic IsingBulk.Anisotropic.NegativeDominance
open IsingBulk.First IsingBulk.Tail IsingBulk.Anisotropic.RegularEdges Set MeasureTheory
open scoped Topology

/-- Parameter-dependent analytic particle weights remain inside the literal
joint analytic density, so all derivative exchanges are proved rather than assumed. -/
theorem weightedAngularDensity_integral_iteratedDeriv
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {mu : Measure X} [IsFiniteMeasureOnCompacts mu] {K : Set X} (hK : IsCompact K)
    {N : ℕ} (hN : 0<N) (Q : X → (Fin N → ℝ)) (hQ : Continuous Q)
    {U : Set ℂ} {curve : ℂ→Coupling} {W : ℂ→ℂ} (hU : IsOpen U)
    (ha : AnalyticOnNhd ℂ curve U) (hW : AnalyticOnNhd ℂ W U)
    (hz : ∀ u∈U, curve u∉spectralSet)
    (hS : ∀ u∈U, IsingBulk.Joint.S (curve u)≠0) (C : ℂ) (j : ℕ) {u : ℂ} (hu : u∈U) :
    iteratedDeriv j (fun v => ∫ x in K, C*(W v*complexAngularDensity (curve v)
      (fun i => (Q x i:ℂ))) ∂mu) u =
      ∫ x in K, C*iteratedDeriv j (fun v => W v*complexAngularDensity (curve v)
        (fun i => (Q x i:ℂ))) u ∂mu := by
  let psi : X → (Fin N → ℂ) := fun x i => (Q x i:ℂ)
  let F : ℂ × (Fin N → ℂ) → ℂ := fun p => W p.1*complexAngularDensity (curve p.1) p.2
  have hp : Continuous psi := continuous_pi (fun i => Complex.continuous_ofReal.comp
    ((continuous_apply i).comp hQ))
  have hF : ∀ v∈U, ∀ x∈K, AnalyticAt ℂ F (v,psi x) := by
    intro v hv x _
    have hd : AnalyticAt ℂ (fun p : ℂ × (Fin N → ℂ) =>
        complexAngularDensity (curve p.1) p.2) (v,psi x) :=
      AnalyticAt.fun_comp_of_eq
        (f := fun p : ℂ × (Fin N → ℂ) => (curve p.1,p.2))
        (g := fun p : Coupling × (Fin N → ℂ) => complexAngularDensity p.1 p.2)
        (complexAngularDensity_joint_analyticAt hN (hz v hv) (hS v hv) (Q x))
        (((ha v hv).comp (f := fun p : ℂ × (Fin N → ℂ) => p.1) analyticAt_fst).prod analyticAt_snd) rfl
    exact ((hW v hv).comp (f := fun p : ℂ × (Fin N → ℂ) => p.1) analyticAt_fst).mul hd
  exact compact_bounded_weight_integral_iteratedDeriv hK hU F psi hp hF
    (fun _ => C) aestronglyMeasurable_const (norm_nonneg C)
    (Filter.Eventually.of_forall (fun _ => le_refl ‖C‖)) j hu

end
end IsingBulk.Joint.Negative
