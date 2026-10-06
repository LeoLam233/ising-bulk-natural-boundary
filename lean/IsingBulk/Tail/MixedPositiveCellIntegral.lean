import IsingBulk.Tail.MixedPairSpectators
import IsingBulk.Tail.MixedPositiveKernel
import IsingBulk.Tail.MixedKernelTransport

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set Filter MeasureTheory
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

theorem mixedSimpleKernel_continuousAt {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hW : ∀ i,0<(sourceW s (deformedPoint f r τ lam θ i)).im)
    (hY : 1-coordinateProduct (deformedPoint f r τ lam θ)≠0)
    (hZ : 1-coordinateProduct (fun i => globalRoot s (deformedPoint f r τ lam θ i))≠0) :
    ContinuousAt (mixedSimpleKernel f r τ lam s) θ := by
  have hy (i : Fin N) : ContinuousAt (fun x => deformedPoint f r τ lam x i) θ :=
    (deformedPoint_fixed_contDiff f r τ lam hp hm i).continuous.continuousAt
  have hYc : ContinuousAt (fun x => coordinateProduct (deformedPoint f r τ lam x)) θ := by
    unfold coordinateProduct
    fun_prop
  have hphase := (mixedContourPhaseSum_spatial_differentiable f hr τ lam s θ hp hm hW).continuousAt
  have hZc : ContinuousAt (fun x => coordinateProduct (fun i => globalRoot s (deformedPoint f r τ lam x i))) θ := by
    simp_rw [mixed_actual_Z_exp]
    exact Complex.continuous_exp.continuousAt.comp (continuousAt_const.mul hphase)
  exact ((continuousAt_const.sub hZc).inv₀ hZ).mul ((continuousAt_const.sub hYc).inv₀ hY)

theorem one_sub_ne_zero_of_exponential_floor {z : ℂ} {a : ℝ} (ha : 0<a)
    (hz : ‖z‖≤Real.exp (-a)) : 1-z≠0 := by
  intro he
  have heq : z=1 := (sub_eq_zero.mp he).symm
  rw [heq,norm_one] at hz
  have hh := Real.exp_lt_one_iff.mpr (neg_neg_of_pos ha)
  linarith

/-- The actual two simple kernels, with the selected branch measure,
integrate on each compact convex positive cell with two logarithmic costs. -/
theorem mixed_positive_cell_kernel_integral {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (j q : Fin N) (hjq : j≠q)
    {S : Set (ℝ × ℝ)} (hSk : IsCompact S) (hSc : Convex ℝ S)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hbox : ∀ p∈S,mixedPairAngles θ j q p∈angleBox N)
    (hplateau : ∀ p∈S,∀ k,k=j ∨ k=q → deriv f.p (mixedPairAngles θ j q p k)=0 ∧
      deriv f.m (mixedPairAngles θ j q p k)=0)
    (hW : ∀ p∈S,∀ i,0<(sourceW s (deformedPoint f r τ lam (mixedPairAngles θ j q p) i)).im)
    (hb : ∀ p∈S,mixedSourceSlope s (deformedPoint f r τ lam (mixedPairAngles θ j q p) j)≠0)
    (hcone : ∀ p∈S,(2/3:ℝ)*‖mixedSourceSlope s (deformedPoint f r τ lam (mixedPairAngles θ j q p) j)‖≤
      (mixedSourceSlope s (deformedPoint f r τ lam (mixedPairAngles θ j q p) j)).re)
    (hsep : ∀ p∈S,‖mixedSourceSlope s (deformedPoint f r τ lam (mixedPairAngles θ j q p) q)/
      mixedSourceSlope s (deformedPoint f r τ lam (mixedPairAngles θ j q p) j)‖≤(1/4:ℝ))
    {aY aZ : ℝ} (haY : 0<aY) (haY1 : aY≤1) (haZ : 0<aZ) (haZ1 : aZ≤1)
    (hY : ∀ p∈S,‖coordinateProduct (deformedPoint f r τ lam (mixedPairAngles θ j q p))‖≤Real.exp (-aY))
    (hZ : ∀ p∈S,‖coordinateProduct (fun i => globalRoot s (deformedPoint f r τ lam (mixedPairAngles θ j q p) i))‖≤Real.exp (-aZ)) :
    IntegrableOn (fun p => ‖mixedSourceSlope s (deformedPoint f r τ lam (mixedPairAngles θ j q p) j)‖*
      ‖mixedSimpleKernel f r τ lam s (mixedPairAngles θ j q p)‖) S ∧
    (∫ p in S, ‖mixedSourceSlope s (deformedPoint f r τ lam (mixedPairAngles θ j q p) j)‖*
      ‖mixedSimpleKernel f r τ lam s (mixedPairAngles θ j q p)‖) ≤
      (48/5:ℝ)*((N:ℝ)*simpleKernelConstant*(1+|Real.log aY|))*
        ((N:ℝ)*simpleKernelConstant*(1+|Real.log aZ|)) := by
  have hSm := hSk.measurableSet
  have hc := mixed_actual_two_phase_coarea f hr τ lam s θ j q hjq hSm hSc hp hm hbox hplateau hW hb hcone hsep haY haY1 haZ haZ1
  have hCont : ContinuousOn (fun p => ‖mixedSourceSlope s (deformedPoint f r τ lam (mixedPairAngles θ j q p) j)‖*
      ‖mixedSimpleKernel f r τ lam s (mixedPairAngles θ j q p)‖) S := by
    intro p hpS
    have hpair := (mixedPairAngles_hasFDerivAt θ j q hjq p).continuousAt
    have hbc := (mixedContourSlope_continuousAt f hr τ lam s _ j hp hm (hW p hpS j)).comp hpair
    have hkc := mixedSimpleKernel_continuousAt f hr τ lam s _ hp hm (hW p hpS)
      (one_sub_ne_zero_of_exponential_floor haY (hY p hpS))
      (one_sub_ne_zero_of_exponential_floor haZ (hZ p hpS))
    exact (hbc.norm.mul (hkc.comp hpair).norm).continuousWithinAt
  have hi := hCont.integrableOn_compact (μ := volume) hSk
  have hpoint (p : ℝ × ℝ) (hpS : p∈S) :
      ‖mixedSourceSlope s (deformedPoint f r τ lam (mixedPairAngles θ j q p) j)‖*
        ‖mixedSimpleKernel f r τ lam s (mixedPairAngles θ j q p)‖ ≤
      4*(‖mixedSourceSlope s (deformedPoint f r τ lam (mixedPairAngles θ j q p) j)‖*
        twoPhaseKernel aY aZ (mixedPairPhase f r τ lam s θ j q p)) := by
    have hk : ‖mixedSimpleKernel f r τ lam s (mixedPairAngles θ j q p)‖≤
        4*twoPhaseKernel aY aZ (mixedPairPhase f r τ lam s θ j q p) := by
      simpa only [mixedSimpleKernel,mixedPairPhase,norm_mul,norm_inv,mul_inv_rev] using
        mixed_actual_positive_kernel f hr τ lam s (mixedPairAngles θ j q p) haY haZ (hY p hpS) (hZ p hpS)
    exact (mul_le_mul_of_nonneg_left hk (norm_nonneg _)).trans_eq (by ring)
  have hdom := hc.1.const_mul (4:ℝ)
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ p in S, 4*(‖mixedSourceSlope s (deformedPoint f r τ lam (mixedPairAngles θ j q p) j)‖*
        twoPhaseKernel aY aZ (mixedPairPhase f r τ lam s θ j q p)) := setIntegral_mono_on hi hdom hSm hpoint
    _ = 4*(∫ p in S, ‖mixedSourceSlope s (deformedPoint f r τ lam (mixedPairAngles θ j q p) j)‖*
        twoPhaseKernel aY aZ (mixedPairPhase f r τ lam s θ j q p)) := integral_const_mul _ _
    _ ≤ 4*((12/5:ℝ)*((N:ℝ)*simpleKernelConstant*(1+|Real.log aY|))*
        ((N:ℝ)*simpleKernelConstant*(1+|Real.log aZ|))) := mul_le_mul_of_nonneg_left hc.2 (by norm_num)
    _ = _ := by ring

end
end IsingBulk.Tail
