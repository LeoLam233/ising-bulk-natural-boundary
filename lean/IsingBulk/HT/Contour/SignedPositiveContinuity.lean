import IsingBulk.HT.Contour.SignedPositiveProduct
import IsingBulk.Tail.AllBranchExteriorPositiveCover
import IsingBulk.Tail.AllBranchExteriorEqualityGeometry

/-! Finite extreme-coordinate cover, applied after taking absolute values.
No derivative of a minimum or maximum selector occurs. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.Branch IsingBulk.Tail IsingBulk.HT.Lie Set MeasureTheory
open scoped BigOperators

theorem signed_positive_kernel_continuousOn {N : ℕ} {d : LocalBranchData}
    (B : BranchEstimates d) (shiftY shiftZ : ℝ) {ε R α β : ℝ} (hε : 0 < ε) (hεr : ε ≤ B.ε₀)
    (hR : 0 ≤ R) (hRB : R ≤ B.r) (hα : 0 < α) (hβ : 0 < β) :
    ContinuousOn (@signedPositiveKernel N d ε α β shiftY shiftZ) (Icc (fun _ => 0) (fun _ => R)) := by
  have hL := allBranchExterior_arclength_continuousOn B ε R hε hεr hRB
  have hprod : ContinuousOn (fun u : Fin N → ℝ => ∏ i, ‖deriv (originalPhase d ε) (u i)‖)
      (Icc (fun _ => 0) (fun _ => R)) := by
    apply continuousOn_finsetProd
    intro i _
    exact hL.comp (continuous_apply i).continuousOn (fun u hu => ⟨by linarith [hu.1 i],hu.2 i⟩)
  have hphase : ContinuousOn (@allBranchExteriorTotalPhase N d ε) (Icc (fun _ => 0) (fun _ => R)) := by
    intro u hu
    exact (allBranchExterior_total_hasFDerivAt B ε hε hεr u
      (fun i => ⟨hu.1 i,(hu.2 i).trans hRB⟩)).continuousAt.continuousWithinAt
  exact hprod.mul ((shiftedTwoPhaseKernel_continuous hα hβ shiftY shiftZ).continuousOn.comp
    (((continuous_finsetSum _ (fun i _ => continuous_apply i)).sub continuous_const).continuousOn.prodMk hphase)
    (fun _ _ => mem_univ _))

end
end IsingBulk.HT.Contour
