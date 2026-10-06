import IsingBulk.Tail.MixedPositiveSpectatorIntegral

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set MeasureTheory Filter
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

/-- Full-dimensional absolute integration of the literal simple kernels
and selected branch measure. All remaining coordinates carry scalar L1
majorants, and both logarithmic costs are explicit. -/
theorem mixed_positive_global_kernel_integral {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (j q : Fin N) (hjq : j≠q)
    {S : Set (Fin N → ℝ)} (hSm : MeasurableSet S) (hSc : Convex ℝ S)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m) (hbox : S⊆angleBox N)
    (hplateau : ∀ θ∈S,∀ k,k=j ∨ k=q → deriv f.p (θ k)=0 ∧ deriv f.m (θ k)=0)
    (hW : ∀ θ∈S,∀ i,0<(sourceW s (deformedPoint f r τ lam θ i)).im)
    (hb : ∀ θ∈S,mixedSourceSlope s (deformedPoint f r τ lam θ j)≠0)
    (hcone : ∀ θ∈S,(2/3:ℝ)*‖mixedSourceSlope s (deformedPoint f r τ lam θ j)‖≤
      (mixedSourceSlope s (deformedPoint f r τ lam θ j)).re)
    (hsep : ∀ θ∈S,‖mixedSourceSlope s (deformedPoint f r τ lam θ q)/
      mixedSourceSlope s (deformedPoint f r τ lam θ j)‖≤(1/4:ℝ))
    (L : ℝ → ℝ) (C : ℝ) (hL0 : ∀ t,0≤L t)
    (hLc : ContinuousOn L (Icc 0 (2*Real.pi))) (hLint : (∫ t in Icc 0 (2*Real.pi),L t)≤C)
    {a b : ℝ} (ha : 0<a) (ha1 : a≤1) (hb' : 0<b) (hb1 : b≤1)
    (hY : ∀ θ∈S,‖coordinateProduct (deformedPoint f r τ lam θ)‖≤Real.exp (-a))
    (hZ : ∀ θ∈S,‖coordinateProduct (fun i => globalRoot s (deformedPoint f r τ lam θ i))‖≤Real.exp (-b)) :
    IntegrableOn (fun θ => ‖mixedSourceSlope s (deformedPoint f r τ lam θ j)‖*
      ‖mixedSimpleKernel f r τ lam s θ‖*(∏ i∈(Finset.univ.erase j).erase q,L (θ i))) S ∧
    (∫ θ in S, ‖mixedSourceSlope s (deformedPoint f r τ lam θ j)‖*
      ‖mixedSimpleKernel f r τ lam s θ‖*(∏ i∈(Finset.univ.erase j).erase q,L (θ i))) ≤
      (48/5:ℝ)*(((N:ℝ)*simpleKernelConstant*(1+|Real.log a|))*
        ((N:ℝ)*simpleKernelConstant*(1+|Real.log b|))*C^(N-2)) := by
  let W := fun θ : Fin N → ℝ => ∏ i∈(Finset.univ.erase j).erase q,L (θ i)
  have hW0 (θ : Fin N → ℝ) : 0≤W θ := Finset.prod_nonneg (fun i _ => hL0 (θ i))
  have hWc : ContinuousOn W S := by
    apply continuousOn_finsetProd
    intro i _
    exact hLc.comp (continuous_apply i).continuousOn (fun θ hθ => ⟨(hbox hθ).1 i,(hbox hθ).2 i⟩)
  have hc := mixed_positive_spectator_integral f hr τ lam s j q hjq hSm hSc hp hm hbox
    hplateau hW hb hcone hsep L C hL0 hLc hLint ha ha1 hb' hb1
  have hCont : ContinuousOn (fun θ => ‖mixedSourceSlope s (deformedPoint f r τ lam θ j)‖*
      ‖mixedSimpleKernel f r τ lam s θ‖*W θ) S := by
    apply ContinuousOn.mul _ hWc
    intro θ hθ
    have hbc := mixedContourSlope_continuousAt f hr τ lam s θ j hp hm (hW θ hθ j)
    have hkc := mixedSimpleKernel_continuousAt f hr τ lam s θ hp hm (hW θ hθ)
      (one_sub_ne_zero_of_exponential_floor ha (hY θ hθ))
      (one_sub_ne_zero_of_exponential_floor hb' (hZ θ hθ))
    exact (hbc.norm.mul hkc.norm).continuousWithinAt
  have hpoint (θ : Fin N → ℝ) (hθ : θ∈S) :
      ‖mixedSourceSlope s (deformedPoint f r τ lam θ j)‖*‖mixedSimpleKernel f r τ lam s θ‖*W θ ≤
      4*(‖mixedSourceSlope s (deformedPoint f r τ lam θ j)‖*
        (twoPhaseKernel a b (∑ i,θ i,(mixedContourPhaseSum f r τ lam s θ).re)*W θ)) := by
    have hk : ‖mixedSimpleKernel f r τ lam s θ‖≤
        4*twoPhaseKernel a b (∑ i,θ i,(mixedContourPhaseSum f r τ lam s θ).re) := by
      simpa only [mixedSimpleKernel,norm_mul,norm_inv,mul_inv_rev] using
        mixed_actual_positive_kernel f hr τ lam s θ ha hb' (hY θ hθ) (hZ θ hθ)
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk
      (norm_nonneg (mixedSourceSlope s (deformedPoint f r τ lam θ j)))) (hW0 θ)
    exact hh.trans_eq (by ring)
  have hdom := hc.1.const_mul (4:ℝ)
  have hi : IntegrableOn (fun θ => ‖mixedSourceSlope s (deformedPoint f r τ lam θ j)‖*
      ‖mixedSimpleKernel f r τ lam s θ‖*W θ) S := by
    apply hdom.mono' (hCont.aestronglyMeasurable hSm)
    apply (ae_restrict_iff' hSm).mpr
    filter_upwards [] with θ hθ
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (hW0 θ))]
    exact hpoint θ hθ
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ θ in S, 4*(‖mixedSourceSlope s (deformedPoint f r τ lam θ j)‖*
        (twoPhaseKernel a b (∑ i,θ i,(mixedContourPhaseSum f r τ lam s θ).re)*W θ)) :=
      setIntegral_mono_on hi hdom hSm hpoint
    _ = 4*(∫ θ in S, ‖mixedSourceSlope s (deformedPoint f r τ lam θ j)‖*
        (twoPhaseKernel a b (∑ i,θ i,(mixedContourPhaseSum f r τ lam s θ).re)*W θ)) := integral_const_mul _ _
    _ ≤ 4*((12/5:ℝ)*(((N:ℝ)*simpleKernelConstant*(1+|Real.log a|))*
        ((N:ℝ)*simpleKernelConstant*(1+|Real.log b|))*C^(N-2))) := mul_le_mul_of_nonneg_left hc.2 (by norm_num)
    _ = _ := by ring

end
end IsingBulk.Tail
