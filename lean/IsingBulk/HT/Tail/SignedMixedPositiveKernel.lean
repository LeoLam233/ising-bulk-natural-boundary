import IsingBulk.Tail.MixedPositiveKernel
import IsingBulk.HT.Tail.SignedCompactSource
import IsingBulk.HT.Lie.SignedBranchKernel

namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail IsingBulk.HT.Lie IsingBulk.HT.Contour Set MeasureTheory Filter
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

/-- The actual two phases, with no frozen occupancy, control both simple poles. -/
theorem signed_mixed_actual_positive_kernel (ξ : ℝ) {N : ℕ} (f : SelectorFunctions)
    {r : ℝ} (hr : 0 < r) (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hy : ‖coordinateProduct (deformedPoint f r τ lam θ)‖ ≤ Real.exp (-a))
    (hz : ‖coordinateProduct (fun i => globalRoot s (deformedPoint f r τ lam θ i))‖ ≤ Real.exp (-b)) :
    ‖(1-(Complex.exp (Complex.I*(ξ:ℂ)))*coordinateProduct (deformedPoint f r τ lam θ))*
      (1-(Complex.exp (Complex.I*(ξ:ℂ)))*coordinateProduct (fun i => globalRoot s (deformedPoint f r τ lam θ i)))‖⁻¹ ≤
      4*shiftedTwoPhaseKernel a b ξ (-ξ) (∑ i, θ i, (mixedContourPhaseSum f r τ lam s θ).re) := by
  rw [mixed_actual_Y_exp f hr τ lam θ] at hy ⊢
  rw [mixed_actual_Z_exp f r τ lam s θ] at hz ⊢
  have hY := signed_exp_kernel_floor (mixedContourLogSum f r τ lam θ) ξ ha hy
  have hZ := signed_exp_kernel_floor (-Complex.I*mixedContourPhaseSum f r τ lam s θ) ξ hb hz
  have hiY : (mixedContourLogSum f r τ lam θ).im = ∑ i, θ i := by
    simp [mixedContourLogSum, logContour]
  have hiZ : (-Complex.I*mixedContourPhaseSum f r τ lam s θ).im =
      -(mixedContourPhaseSum f r τ lam s θ).re := by simp [Complex.mul_im]
  rw [hiY] at hY
  unfold shiftedPhaseKernel at hY hZ
  rw [hiZ,show -(mixedContourPhaseSum f r τ lam s θ).re+ξ =
    -((mixedContourPhaseSum f r τ lam s θ).re+ -ξ) by ring,phaseDenominator_neg] at hZ
  have hh := mul_le_mul hY hZ (inv_nonneg.mpr (norm_nonneg _)) (by
    unfold phaseDenominator
    positivity)
  rw [norm_mul,mul_inv_rev]
  unfold shiftedTwoPhaseKernel shiftedPhaseKernel
  convert hh using 1 <;> ring

theorem signedMixedSimpleKernel_continuousAt (σ : ℂ) {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hW : ∀ i,0<(sourceW s (deformedPoint f r τ lam θ i)).im)
    (hY : 1-σ*coordinateProduct (deformedPoint f r τ lam θ)≠0)
    (hZ : 1-σ*coordinateProduct (fun i => globalRoot s (deformedPoint f r τ lam θ i))≠0) :
    ContinuousAt (signedMixedSimpleKernel σ f r τ lam s) θ := by
  have hy (i : Fin N) : ContinuousAt (fun x => deformedPoint f r τ lam x i) θ :=
    (deformedPoint_fixed_contDiff f r τ lam hp hm i).continuous.continuousAt
  have hYc : ContinuousAt (fun x => coordinateProduct (deformedPoint f r τ lam x)) θ := by
    unfold coordinateProduct
    fun_prop
  have hphase := (mixedContourPhaseSum_spatial_differentiable f hr τ lam s θ hp hm hW).continuousAt
  have hZc : ContinuousAt (fun x => coordinateProduct (fun i => globalRoot s (deformedPoint f r τ lam x i))) θ := by
    simp_rw [mixed_actual_Z_exp]
    exact Complex.continuous_exp.continuousAt.comp (continuousAt_const.mul hphase)
  exact ((continuousAt_const.sub (continuousAt_const.mul hZc)).inv₀ hZ).mul ((continuousAt_const.sub (continuousAt_const.mul hYc)).inv₀ hY)


end
end IsingBulk.HT.Tail
