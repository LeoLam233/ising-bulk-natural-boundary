import IsingBulk.HT22.Tail.CoordinateCalculus
import IsingBulk.HT22.Tail.FrameCalculus

/-! Exact change from the published moving-q frame to the F001 fixed-v frame.
This is a scalar differential-operator identity, not a transport estimate. -/
namespace IsingBulk.HT22.SeedFrameConversion
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Tail
open scoped BigOperators Topology ContDiff Matrix.Norms.Elementwise
set_option backward.isDefEq.respectTransparency false

theorem parameterFrame_eq_shared {N : ℕ} (τ δ : ℝ) (p m : ℝ → ℝ)
    (F : ℂ → (Fin N → ℝ) → ℂ) (t : ℂ) (θ : Fin N → ℝ)
    (h : PreferredFramePoint τ δ p m t θ) :
    parameterFrame τ p m F t θ = preferredParameterFrame τ p m F t θ -
      deriv preferredMovingBranch t * ∑ a, preferredCoordinateFrame τ p m a F t θ := by
  have hu (a : Fin N) := inverseT_moving_adapter t (sourceCoordinate τ p m t θ a)
    (framePoint_inverse_analytic h a)
    (preferredMovingBranch_analyticAt_upper t h.trace_im).differentiableAt
  simp_rw [sourceCoordinate_moving_adapter] at hu
  simp only [parameterFrame,preferredParameterFrame,preferredCoordinateFrame,
    Matrix.mulVec,dotProduct]
  simp_rw [hu,inverseV_moving_adapter,sourceCoordinate_moving_adapter]
  simp only [mul_sub,Finset.sum_sub_distrib,sub_mul,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm (f := fun a i => deriv preferredMovingBranch t *
    ((preferredContourMatrix τ p m θ)⁻¹ i a *
      preferredSourceUQ t (preferredSourceCoordinate τ p m t θ a) *
        deriv (fun x : ℝ => F t (Function.update θ i x)) (θ i)))]
  rw [← add_sub_assoc]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro a _
  ring

end
end IsingBulk.HT22.SeedFrameConversion
