import IsingBulk.Tail.MixedPhaseSpectatorIntegral
import IsingBulk.Tail.MixedPositiveCellIntegral

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set MeasureTheory Filter
open scoped Topology BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

theorem mixedPhaseSpectatorKernel_factorization {N : ℕ} (f : SelectorFunctions)
    (r τ lam : ℝ) (s : ℂ) (j q : Fin N) (hjq : j≠q) (a b : ℝ) (L : ℝ → ℝ) (θ : Fin N → ℝ) :
    weightedPhaseSpectatorKernel j q a b L (mixedCoordinatePhase f r τ lam s j q θ)=
      twoPhaseKernel a b (∑ i,θ i,(mixedContourPhaseSum f r τ lam s θ).re)*
        ∏ i∈(Finset.univ.erase j).erase q,L (θ i) := by
  rw [weightedPhaseSpectatorKernel_factorization j q hjq]
  have hp : (∏ i∈(Finset.univ.erase j).erase q,L (mixedCoordinatePhase f r τ lam s j q θ i))=
      ∏ i∈(Finset.univ.erase j).erase q,L (θ i) := by
    apply Finset.prod_congr rfl
    intro i hi
    have hiq := (Finset.mem_erase.mp hi).1
    have hij := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    simp only [mixedCoordinatePhase,twoPhaseUpdate,hij,hiq,ite_false]
  rw [hp]
  simp only [coordinatePhaseKernel,mixedCoordinatePhase,twoPhaseUpdate,ite_true,hjq.symm,ite_false,twoPhaseKernel]

/-- Full-dimensional positive mixed coarea. The unchanged spectator
coordinates pay their L1 costs, without freezing their source dependence. -/
theorem mixed_positive_spectator_integral {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
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
    {a b : ℝ} (ha : 0<a) (ha1 : a≤1) (hb' : 0<b) (hb1 : b≤1) :
    IntegrableOn (fun θ => ‖mixedSourceSlope s (deformedPoint f r τ lam θ j)‖*
      (twoPhaseKernel a b (∑ i,θ i,(mixedContourPhaseSum f r τ lam s θ).re)*
        ∏ i∈(Finset.univ.erase j).erase q,L (θ i))) S ∧
    (∫ θ in S, ‖mixedSourceSlope s (deformedPoint f r τ lam θ j)‖*
      (twoPhaseKernel a b (∑ i,θ i,(mixedContourPhaseSum f r τ lam s θ).re)*
        ∏ i∈(Finset.univ.erase j).erase q,L (θ i))) ≤
      (12/5:ℝ)*(((N:ℝ)*simpleKernelConstant*(1+|Real.log a|))*
        ((N:ℝ)*simpleKernelConstant*(1+|Real.log b|))*C^(N-2)) := by
  let T := mixedCoordinatePhase f r τ lam s j q
  let T' := mixedCoordinatePhaseDerivative f r τ lam s j q
  have hki := mixed_phase_spectator_kernel_integral hjq L C hL0 ha ha1 hb' hb1 hLc hLint
  have hRatio (θ : Fin N → ℝ) (hθ : θ∈S) :
      ‖mixedSourceSlope s (deformedPoint f r τ lam θ j)‖≤(12/5:ℝ)*|(T' θ).det| := by
    rw [mixedCoordinatePhaseDerivative_det f hr τ lam s j q hjq θ hp hm (hplateau θ hθ) (hW θ hθ),abs_neg]
    have hh := (mixed_jacobian_margin (hb θ hθ) (hcone θ hθ) (hsep θ hθ)).1
    have hh' := le_abs_self (mixedSourceSlope s (deformedPoint f r τ lam θ j)-
      mixedSourceSlope s (deformedPoint f r τ lam θ q)).re
    nlinarith
  have hmain := injective_coordinate_weighted_coarea_on hSm T T'
    (fun θ hθ => (mixedCoordinatePhase_hasFDerivAt f hr τ lam s j q θ hp hm (hW θ hθ)).hasFDerivWithinAt)
    (mixedCoordinatePhase_injOn f hr τ lam s j q hjq hSc hp hm hplateau hW hb hcone hsep)
    (mixedCoordinatePhase_image f r τ lam s j q hbox hW)
    (fun θ => ‖mixedSourceSlope s (deformedPoint f r τ lam θ j)‖)
    (weightedPhaseSpectatorKernel j q a b L)
    (fun θ hθ => (mixedContourSlope_continuousAt f hr τ lam s θ j hp hm (hW θ hθ j)).norm.continuousWithinAt)
    (mixedPhaseSpectatorKernel_continuousOn j q ha hb' L hLc)
    (weightedPhaseSpectatorKernel_nonneg j q a b L hL0) hki.1
    (by norm_num : (0:ℝ)≤12/5) (fun _ _ => norm_nonneg _) hRatio
  dsimp only [T] at hmain
  simp_rw [mixedPhaseSpectatorKernel_factorization f r τ lam s j q hjq] at hmain
  exact ⟨hmain.1,hmain.2.trans (mul_le_mul_of_nonneg_left hki.2 (by norm_num))⟩

end
end IsingBulk.Tail
