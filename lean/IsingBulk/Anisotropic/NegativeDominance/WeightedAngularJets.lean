import IsingBulk.Anisotropic.RegularEdges.ComplexAngularParameterJets

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.Anisotropic.RegularEdges Set MeasureTheory
open scoped Topology

/-- Parameter-dependent analytic particle weights remain inside the literal
joint analytic density, so all derivative exchanges are proved rather than assumed. -/
theorem weightedAngularDensity_integral_iteratedDeriv
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {mu : Measure X} [IsFiniteMeasureOnCompacts mu] {K : Set X} (hK : IsCompact K)
    {N : ℕ} (hN : 0<N) (Q : X → (Fin N → ℝ)) (hQ : Continuous Q)
    {lam : ℝ} {U : Set ℂ} {zeta W : ℂ → ℂ} (hU : IsOpen U)
    (ha : AnalyticOnNhd ℂ zeta U) (hW : AnalyticOnNhd ℂ W U)
    (hz : ∀ u∈U, zeta u∉spectralSet lam)
    (hS : ∀ u∈U, spectralS (zeta u)≠0) (C : ℂ) (j : ℕ) {u : ℂ} (hu : u∈U) :
    iteratedDeriv j (fun v => ∫ x in K, C*(W v*complexAngularDensity lam (zeta v)
      (fun i => (Q x i:ℂ))) ∂mu) u =
      ∫ x in K, C*iteratedDeriv j (fun v => W v*complexAngularDensity lam (zeta v)
        (fun i => (Q x i:ℂ))) u ∂mu := by
  let psi : X → (Fin N → ℂ) := fun x i => (Q x i:ℂ)
  let F : ℂ × (Fin N → ℂ) → ℂ := fun p => W p.1*complexAngularDensity lam (zeta p.1) p.2
  have hp : Continuous psi := continuous_pi (fun i => Complex.continuous_ofReal.comp
    ((continuous_apply i).comp hQ))
  have hF : ∀ v∈U, ∀ x∈K, AnalyticAt ℂ F (v,psi x) := by
    intro v hv x _
    have hd : AnalyticAt ℂ (fun p : ℂ × (Fin N → ℂ) =>
        complexAngularDensity lam (zeta p.1) p.2) (v,psi x) :=
      AnalyticAt.fun_comp_of_eq
        (f := fun p : ℂ × (Fin N → ℂ) => (zeta p.1,p.2))
        (g := fun p : ℂ × (Fin N → ℂ) => complexAngularDensity lam p.1 p.2)
        (complexAngularDensity_joint_analyticAt hN (hz v hv) (hS v hv) (Q x))
        (((ha v hv).comp (f := fun p : ℂ × (Fin N → ℂ) => p.1) analyticAt_fst).prod analyticAt_snd) rfl
    exact ((hW v hv).comp (f := fun p : ℂ × (Fin N → ℂ) => p.1) analyticAt_fst).mul hd
  exact compact_bounded_weight_integral_iteratedDeriv hK hU F psi hp hF
    (fun _ => C) aestronglyMeasurable_const (norm_nonneg C)
    (Filter.Eventually.of_forall (fun _ => le_refl ‖C‖)) j hu

end
end IsingBulk.Anisotropic.NegativeDominance
