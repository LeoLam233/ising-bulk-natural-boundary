import IsingBulk.Tail.OriginalMicrocoreChart
import IsingBulk.Tail.MicrocoreBranchProduct
import IsingBulk.Tail.MicrocoreWindow

/-! The source top-form Jacobian is the actual branch arclength product. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets IsingBulk.Branch IsingBulk.Lie
open scoped BigOperators

theorem original_chartPhase_eq (d : LocalBranchData) (ε u : ℝ) :
    chartPhase (radialParameter d.theta ε) (-d.c₀*ε) d.thetaB (u:ℂ)=originalPhase d ε u := by
  unfold chartPhase originalPhase currentPhase
  rw [original_chartW_eq]
  rfl

theorem original_deriv_eq_chartB (d : LocalBranchData) (ε u : ℝ)
    (hr : 0 < (originalW d ε u).re) (hi : 0 < (originalW d ε u).im) :
    deriv (originalPhase d ε) u=
      chartB (radialParameter d.theta ε) (-d.c₀*ε) d.thetaB (u:ℂ) := by
  have hh := chartPhase_real_angular (radialParameter d.theta ε) (-d.c₀*ε) d.thetaB u
    (by simpa only [original_chartW_eq] using hr) (by simpa only [original_chartW_eq] using hi)
  have he : (fun t : ℝ => chartPhase (radialParameter d.theta ε) (-d.c₀*ε) d.thetaB (t:ℂ)) =
      originalPhase d ε := funext (original_chartPhase_eq d ε)
  rw [he] at hh
  exact hh.deriv

theorem original_chartJacobian_norm {n : ℕ} (d : LocalBranchData) (ε : ℝ) (u : AngularSpace n)
    (hr : ∀ i, 0 < (originalW d ε (u i)).re) (hi : ∀ i, 0 < (originalW d ε (u i)).im) :
    ‖chartJacobian (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u‖=
      ∏ i, ‖deriv (originalPhase d ε) (u i)‖ := by
  unfold chartJacobian
  rw [norm_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [original_deriv_eq_chartB d ε (u i) (hr i) (hi i)]

theorem original_chartMap_eq {n : ℕ} (d : LocalBranchData) (ε : ℝ) (u : AngularSpace n) :
    chartMap (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u =
      fun i => originalPhase d ε (u i) := by
  funext i
  exact original_chartPhase_eq d ε (u i)

 theorem original_angularY_eq (d : LocalBranchData) (ε u : ℝ) :
    angularY (-d.c₀*ε) d.thetaB (u:ℂ)=microcoreY d.c₀ ε d.thetaB u := by
  unfold angularY microcoreY
  congr 1
  push_cast
  ring

 theorem original_regularYProduct_eq {n : ℕ} (d : LocalBranchData) (ε : ℝ) (u : AngularSpace n)
    (hg : ∀ i, 0 < (angularG (-d.c₀*ε) d.thetaB (u i)).re) :
    regularYProduct (radialParameter d.theta ε)
      (chartMap (-d.c₀*ε) d.thetaB (radialParameter d.theta ε) u) =
      ∏ i, microcoreY d.c₀ ε d.thetaB (u i) := by
  unfold regularYProduct
  apply Finset.prod_congr rfl
  intro i _
  rw [chartMap,regularY_chartPhase _ _ _ _ (hg i),original_angularY_eq]

end
end IsingBulk.Tail
