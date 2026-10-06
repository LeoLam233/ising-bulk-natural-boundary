import IsingBulk.Tail.AllBranchExteriorPositiveCoarea
import IsingBulk.Tail.CompactPairCoordinates
import IsingBulk.Tail.PairPhaseInjectivity

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch Set
open scoped BigOperators

def allBranchExteriorTotalPhase {N : ℕ} (d : LocalBranchData) (ε : ℝ) (u : Fin N → ℝ) : ℝ :=
  ∑ i, originalRealPhase d ε (u i)

def allBranchExteriorTotalDerivative {N : ℕ} (d : LocalBranchData) (ε : ℝ) (u : Fin N → ℝ) :
    (Fin N → ℝ) →L[ℝ] ℝ :=
  ∑ i, deriv (originalRealPhase d ε) (u i) • (ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ)

theorem allBranchExterior_total_hasFDerivAt {N : ℕ} {d : LocalBranchData}
    (B : BranchEstimates d) (ε : ℝ) (hε : 0 < ε) (hεr : ε ≤ B.ε₀)
    (u : Fin N → ℝ) (hu : ∀ i, 0 ≤ u i ∧ u i ≤ B.r) :
    HasFDerivAt (allBranchExteriorTotalPhase d ε) (allBranchExteriorTotalDerivative d ε u) u := by
  apply HasFDerivAt.fun_sum
  intro i _
  have hd := (allBranchExterior_realPhase_differentiable B ε (u i) hε hεr (hu i).1 (hu i).2).hasDerivAt
  convert! hd.comp_hasFDerivAt u (ContinuousLinearMap.proj i : (Fin N → ℝ) →L[ℝ] ℝ).hasFDerivAt using 1

theorem allBranchExterior_total_pair_direction {N : ℕ} (d : LocalBranchData) (ε : ℝ)
    (u : Fin N → ℝ) (p q : Fin N) :
    allBranchExteriorTotalDerivative d ε u (pairDirection p q)=
      deriv (originalRealPhase d ε) (u p)-deriv (originalRealPhase d ε) (u q) := by
  simp [allBranchExteriorTotalDerivative,pairDirection,Finset.sum_sub_distrib,mul_sub,Pi.single_apply,mul_ite]

def allBranchExteriorCoordinateMap {N : ℕ} (d : LocalBranchData) (ε : ℝ) (p q : Fin N) :
    (Fin N → ℝ) → (Fin N → ℝ) :=
  twoPhaseUpdate (fun u => (∑ i, u i)-(N:ℝ)*d.thetaB) (allBranchExteriorTotalPhase d ε) p q

theorem allBranchExterior_coordinate_hasFDerivAt {N : ℕ} {d : LocalBranchData}
    (B : BranchEstimates d) (ε : ℝ) (hε : 0 < ε) (hεr : ε ≤ B.ε₀)
    (u : Fin N → ℝ) (hu : ∀ i, 0 ≤ u i ∧ u i ≤ B.r) (p q : Fin N) :
    HasFDerivAt (allBranchExteriorCoordinateMap d ε p q)
      (twoPhaseUpdateDeriv (coordinateSumLinear N) (allBranchExteriorTotalDerivative d ε u) p q) u := by
  apply twoPhaseUpdate_hasFDerivAt _ (allBranchExterior_total_hasFDerivAt B ε hε hεr u hu)
  have hh := (coordinateSumLinear N).hasFDerivAt (x := u)
  have he : (fun y : Fin N → ℝ => (∑ i, y i)-(N:ℝ)*d.thetaB)=
      (fun y => coordinateSumLinear N y-(N:ℝ)*d.thetaB) := by
    funext y
    rw [coordinateSumLinear_apply]
  rw [he]
  exact hh.sub_const _

theorem allBranchExterior_coordinate_det {N : ℕ} (d : LocalBranchData) (ε : ℝ)
    (u : Fin N → ℝ) (p q : Fin N) (hpq : p ≠ q) :
    (twoPhaseUpdateDeriv (coordinateSumLinear N) (allBranchExteriorTotalDerivative d ε u) p q).det=
      deriv (originalRealPhase d ε) (u q)-deriv (originalRealPhase d ε) (u p) := by
  rw [sumPhaseUpdate_det _ hpq,allBranchExterior_total_pair_direction]
  ring

end
end IsingBulk.Tail
