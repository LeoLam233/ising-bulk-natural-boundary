import IsingBulk.Tail.MixedActualAmplitudeJets
import IsingBulk.Tail.MixedHybridAmplitude

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false

@[simp] theorem mixedActiveAmplitudeVertex_zero {N : ℕ} (J : Finset (Fin N)) (q : Fin N)
    (s : ℂ) (φ y : Fin N → ℂ) (a : Fin 3) (i : Fin N) :
    mixedActiveAmplitudeVertex J q s φ y a i 0=
      if i∈J then mixedBranchAmplitudeFactor a s (φ i) else mixedCompactAmplitudeFactor a s (y i) := by
  unfold mixedActiveAmplitudeVertex
  split_ifs <;> simp [mixedActiveBranch,mixedActiveCompact,rotatingCompactCoefficient_formula]

theorem mixedActiveAmplitudeVertex_onebody_source {N : ℕ} (J : Finset (Fin N)) (q : Fin N)
    (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (i : Fin N)
    (hW : 0<(sourceW s (deformedPoint f r τ lam θ i)).im) :
    mixedActiveAmplitudeVertex J q s (fun i => mixedSourcePhase s (deformedPoint f r τ lam θ i))
      (deformedPoint f r τ lam θ) 0 i 0=mixedSourceOneBody J f r τ lam s θ i := by
  rw [mixedActiveAmplitudeVertex_zero]
  unfold mixedSourceOneBody
  split_ifs
  · rfl
  · change _*residueFactor (selectedContinuedRoot s _)=_
    rw [show selectedContinuedRoot s (deformedPoint f r τ lam θ i)=globalRoot s (deformedPoint f r τ lam θ i)
      from continuedRoot_eq_interiorRoot hW]

theorem mixedActiveAmplitudeVertex_inverse_root_source {N : ℕ} (J : Finset (Fin N)) (q : Fin N)
    (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (i : Fin N)
    (hW : 0<(sourceW s (deformedPoint f r τ lam θ i)).im) :
    mixedActiveAmplitudeVertex J q s (fun i => mixedSourcePhase s (deformedPoint f r τ lam θ i))
      (deformedPoint f r τ lam θ) 1 i 0=(globalRoot s (deformedPoint f r τ lam θ i))⁻¹ := by
  rw [mixedActiveAmplitudeVertex_zero]
  split_ifs
  · change Complex.exp (Complex.I*mixedSourcePhase s _)=(globalRoot s _)⁻¹
    rw [globalRoot_eq_exp_lowerArccos,← Complex.exp_neg]
    congr 1
    unfold mixedSourcePhase
    ring
  · change (selectedContinuedRoot s _)⁻¹=_
    rw [show selectedContinuedRoot s (deformedPoint f r τ lam θ i)=globalRoot s (deformedPoint f r τ lam θ i)
      from continuedRoot_eq_interiorRoot hW]

theorem mixedActiveAmplitudeVertex_inverse_y_source {N : ℕ} (J : Finset (Fin N)) (q : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (i : Fin N)
    (hsin : i∈J → Real.sin (θ i)<0) :
    mixedActiveAmplitudeVertex J q s (fun i => mixedSourcePhase s (deformedPoint f r τ lam θ i))
      (deformedPoint f r τ lam θ) 2 i 0=(deformedPoint f r τ lam θ i)⁻¹ := by
  rw [mixedActiveAmplitudeVertex_zero]
  split_ifs with hi
  · change (regularY s (mixedContourPhase f r τ lam s θ i))⁻¹=_
    rw [mixed_actual_regularY f hr τ lam s θ i (hsin hi)]
  · rfl

theorem mixedActiveSmoothAmplitude_source {N : ℕ} (J : Finset (Fin N)) (q : Fin N)
    (f : SelectorFunctions) {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hsin : ∀ i∈J,Real.sin (θ i)<0)
    (hW : ∀ i,0<(sourceW s (deformedPoint f r τ lam θ i)).im) :
    mixedActiveSmoothAmplitude J q s (fun i => mixedSourcePhase s (deformedPoint f r τ lam θ i))
      (deformedPoint f r τ lam θ) 0=
      ((coordinateProduct (fun i => globalRoot s (deformedPoint f r τ lam θ i)))⁻¹+
        (coordinateProduct (deformedPoint f r τ lam θ))⁻¹)*
        ∏ i,mixedSourceOneBody J f r τ lam s θ i := by
  unfold mixedActiveSmoothAmplitude
  simp_rw [mixedActiveAmplitudeVertex_onebody_source J q f r τ lam s θ _ (hW _),
    mixedActiveAmplitudeVertex_inverse_root_source J q f r τ lam s θ _ (hW _),
    mixedActiveAmplitudeVertex_inverse_y_source J q f hr τ lam s θ _ (hsin _)]
  simp only [coordinateProduct,Finset.prod_inv_distrib]

end
end IsingBulk.Tail
