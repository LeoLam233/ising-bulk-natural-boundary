import IsingBulk.HT22.Far.WholeTail
import IsingBulk.HT22.Tail.PhysicalSigns
namespace IsingBulk.HT22.FullTail
noncomputable section
open IsingBulk.Preferred22

theorem transportedIntegral_eq_whole (negative : Bool) (b : PreferredBranchData)
    (B : PreferredCoareaBump b) (r : ℝ → ℝ) (j n : ℕ) (ε τ : ℝ) :
    Tail.transportedIntegral negative (2*n+2) B.delta τ preferredPopulationCutoff B.p B.m r j
      (IsingBulk.Branch.radialParameter b.alpha ε) =
    Far.wholeTransportedIntegral b B r j (Physical.constraintAngle negative)
      (Physical.constraintAngle negative) n ε τ := by
  unfold Tail.transportedIntegral Far.wholeTransportedIntegral
  rw [Tail.constraintSign_eq_signed_exp]
  rfl
end
end IsingBulk.HT22.FullTail
