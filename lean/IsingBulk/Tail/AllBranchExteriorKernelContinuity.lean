import IsingBulk.Tail.AllBranchExteriorNegativeDensity

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch IsingBulk.Jets IsingBulk.Lie Set MeasureTheory
open scoped BigOperators

theorem allBranchExterior_kernel_density_source_norm {n : ℕ} (d : LocalBranchData) (ε : ℝ)
    (u : AngularSpace n)
    (hp : MicrocoreJetPoint (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u) :
    allBranchExteriorKernelDensity d ε u=
      ‖sourceComplexDensity (-d.c₀*ε) d.thetaB (fun _ : ℂ × (Fin (n+1) → ℂ) => 1)
        (realAngularEmbedding (radialParameter d.theta ε,u))‖ := by
  have hr (i : Fin (n+1)) : 0 < (originalW d ε (u i)).re := by
    simpa only [original_chartW_eq] using hp.re_pos i
  have hi (i : Fin (n+1)) : 0 < (originalW d ε (u i)).im := by
    simpa only [original_chartW_eq] using hp.im_pos i
  change _ = ‖chartJacobian (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u*
    (1/regularKernel (radialParameter d.theta ε) (chartMap (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u))‖
  rw [norm_mul,norm_div,norm_one,original_chartJacobian_norm d ε u hr hi,original_chartMap_eq]
  unfold allBranchExteriorKernelDensity
  ring

theorem allBranchExterior_kernel_density_continuousOn {n : ℕ} (d : LocalBranchData)
    {ε : ℝ} (hε : 0 < ε) (S : Set (AngularSpace n))
    (hp : ∀ u ∈ S, MicrocoreJetPoint (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u) :
    ContinuousOn (allBranchExteriorKernelDensity d ε) S := by
  have hv : -d.c₀*ε < 0 := by nlinarith [d.c₀_pos]
  have hc : ContinuousOn (fun u : AngularSpace n =>
      ‖sourceComplexDensity (-d.c₀*ε) d.thetaB (fun _ : ℂ × (Fin (n+1) → ℂ) => 1)
        (realAngularEmbedding (radialParameter d.theta ε,u))‖) S := by
    intro u hu
    have hA := allBranchExterior_density_analytic_of_micro (-d.c₀*ε) d.thetaB hv
      (fun _ : ℂ × (Fin (n+1) → ℂ) => 1) (radialParameter d.theta ε) u (hp u hu) analyticAt_const
    have he : Continuous (fun w : AngularSpace n => realAngularEmbedding (radialParameter d.theta ε,w)) :=
      (realAngularEmbedding_contDiff (n+1)).continuous.comp (continuous_const.prodMk continuous_id)
    exact (hA.continuousAt.comp
      (f := fun w : AngularSpace n => realAngularEmbedding (radialParameter d.theta ε,w))
      he.continuousAt).norm.continuousWithinAt
  exact hc.congr (fun u hu => allBranchExterior_kernel_density_source_norm d ε u (hp u hu))

theorem allBranchExterior_kernel_density_nonneg {N : ℕ} (d : LocalBranchData) (ε : ℝ)
    (u : Fin N → ℝ) : 0 ≤ allBranchExteriorKernelDensity d ε u :=
  div_nonneg (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) (norm_nonneg _)

end
end IsingBulk.Tail
