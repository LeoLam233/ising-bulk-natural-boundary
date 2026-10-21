import IsingBulk.HT.Lie.SignedPhysicalIntegral
import IsingBulk.Tail.AllBranchExteriorKernelContinuity

/-! The literal signed kernel density shared by signed positive/negative
coarea and the actual differentiated Lie-source estimates. -/
namespace IsingBulk.HT.Lie
noncomputable section
open IsingBulk.Branch IsingBulk.Jets IsingBulk.Lie IsingBulk.Tail Set MeasureTheory
open scoped BigOperators

def signedExteriorKernelDensity {N : ℕ} (σ : ℂ) (d : LocalBranchData) (ε : ℝ)
    (u : Fin N → ℝ) : ℝ :=
  (∏ i, ‖deriv (originalPhase d ε) (u i)‖)/
    ‖signedRegularKernel σ (radialParameter d.theta ε) (fun i => originalPhase d ε (u i))‖

theorem signed_kernel_density_nonneg {N : ℕ} (σ : ℂ) (d : LocalBranchData)
    (ε : ℝ) (u : Fin N → ℝ) : 0 ≤ signedExteriorKernelDensity σ d ε u :=
  div_nonneg (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) (norm_nonneg _)

theorem signed_kernel_density_source_norm {n : ℕ} (σ : ℂ) (d : LocalBranchData)
    (ε : ℝ) (u : AngularSpace n)
    (hp : MicrocoreJetPoint (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u) :
    signedExteriorKernelDensity σ d ε u =
      ‖signedComplexDensity σ (-d.c₀*ε) d.thetaB (fun _ : ℂ × (Fin (n+1) → ℂ) => 1)
        (realAngularEmbedding (radialParameter d.theta ε,u))‖ := by
  have hr (i : Fin (n+1)) : 0 < (originalW d ε (u i)).re := by
    simpa only [original_chartW_eq] using hp.re_pos i
  have hi (i : Fin (n+1)) : 0 < (originalW d ε (u i)).im := by
    simpa only [original_chartW_eq] using hp.im_pos i
  change _ = ‖chartJacobian (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u*
    (1/signedRegularKernel σ (radialParameter d.theta ε)
      (chartMap (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u))‖
  rw [norm_mul,norm_div,norm_one,original_chartJacobian_norm d ε u hr hi,original_chartMap_eq]
  unfold signedExteriorKernelDensity
  ring

theorem signed_kernel_density_eq_chart {n : ℕ} (σ : ℂ) (d : LocalBranchData)
    (ε : ℝ) (u : AngularSpace n)
    (hp : MicrocoreJetPoint (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u) :
    signedExteriorKernelDensity σ d ε u =
      ‖chartJacobian (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u‖/
        ‖signedRegularKernel σ (radialParameter d.theta ε)
          (chartMap (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u)‖ := by
  rw [signed_kernel_density_source_norm σ d ε u hp]
  change ‖chartJacobian (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u*
    (1/signedRegularKernel σ (radialParameter d.theta ε)
      (chartMap (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u))‖ = _
  rw [norm_mul,norm_div,norm_one]
  ring

theorem signed_kernel_density_continuousOn {n : ℕ} (σ : ℂ) (d : LocalBranchData)
    {ε : ℝ} (S : Set (AngularSpace n))
    (hp : ∀ u∈S, MicrocoreJetPoint (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u)
    (hσ : ∀ u∈S, signedRegularKernel σ (radialParameter d.theta ε)
      (chartMap (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u) ≠ 0) :
    ContinuousOn (signedExteriorKernelDensity σ d ε) S := by
  have hc : ContinuousOn (fun u : AngularSpace n =>
      ‖signedComplexDensity σ (-d.c₀*ε) d.thetaB (fun _ : ℂ × (Fin (n+1) → ℂ) => 1)
        (realAngularEmbedding (radialParameter d.theta ε,u))‖) S := by
    intro u hu
    have hA := signed_density_analytic_of_micro σ (-d.c₀*ε) d.thetaB
      (fun _ : ℂ × (Fin (n+1) → ℂ) => 1) (radialParameter d.theta ε) u
      (hp u hu) analyticAt_const (hσ u hu)
    have he : Continuous (fun w : AngularSpace n => realAngularEmbedding (radialParameter d.theta ε,w)) :=
      (realAngularEmbedding_contDiff (n+1)).continuous.comp (continuous_const.prodMk continuous_id)
    exact (hA.continuousAt.comp
      (f := fun w : AngularSpace n => realAngularEmbedding (radialParameter d.theta ε,w))
      he.continuousAt).norm.continuousWithinAt
  exact hc.congr (fun u hu => signed_kernel_density_source_norm σ d ε u (hp u hu))

end
end IsingBulk.HT.Lie
