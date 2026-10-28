import IsingBulk.HT22.Physical.DerivativePartition
import IsingBulk.HT22.Selected.AbsoluteTail
import IsingBulk.HT22.Anchor.AbsoluteSummation
namespace IsingBulk.HT22.FullTail
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Physical IsingBulk.HT22.Selected
open scoped BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

theorem signed_coefficient_norm_le (negative : Bool) (k : ℕ)
    (d : PreferredBranchData) (B : PreferredCoareaBump d) {τ ε : ℝ}
    (hτ : 0≤τ) (hε : 0<ε) (r : ℝ → ℝ) (hr : ContDiff ℝ ∞ r) (j : ℕ) :
    ‖iteratedDeriv j (signedCoefficient negative (2*(k+1)+1))
      (IsingBulk.Branch.radialParameter d.alpha ε)‖ ≤
    ‖iteratedDeriv j (selectedIntegral negative (2*(k+1)) τ B.p B.m)
      (IsingBulk.Branch.radialParameter d.alpha ε)‖ +
    2*(‖iteratedDeriv j (rightPopulationIntegral negative (2*(k+1)) τ
      preferredPopulationCutoff B.p B.m r) (IsingBulk.Branch.radialParameter d.alpha ε)‖ +
      Anchor.derivativeMass negative k τ B.p B.m r j (IsingBulk.Branch.radialParameter d.alpha ε)) := by
  have hn : 1<‖IsingBulk.Branch.radialParameter d.alpha ε‖ := by
    rw [IsingBulk.First.radialParameter_norm hε.le]
    linarith
  have hS : 0<(temperatureTrace (IsingBulk.Branch.radialParameter d.alpha ε)).im :=
    preferredRadialTrace_im_pos d hε
  rw [complete_derivative_partition negative (2*(k+1)) d B hτ r hr j hn hS]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact le_rfl
  rw [norm_mul,show ‖(2:ℂ)‖=(2:ℝ) by norm_num]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply (norm_add_le _ _).trans
  gcongr
  exact norm_sum_le _ _

end
end IsingBulk.HT22.FullTail
