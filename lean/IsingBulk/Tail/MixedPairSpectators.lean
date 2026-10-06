import IsingBulk.Tail.MixedCoareaChart
import IsingBulk.Tail.MixedHybridDensity
import IsingBulk.Tail.SelectorOriginal

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First Set
open scoped BigOperators

theorem mixedPairAngles_spectator {N : ℕ} (θ : Fin N → ℝ) (j q i : Fin N)
    (hij : i≠j) (hiq : i≠q) (p : ℝ × ℝ) : mixedPairAngles θ j q p i=θ i := by
  simp [mixedPairAngles,Function.update_of_ne,hij,hiq]

theorem mixedPairAngles_selected {N : ℕ} (θ : Fin N → ℝ) (j q : Fin N)
    (hjq : j≠q) (p : ℝ × ℝ) :
    mixedPairAngles θ j q p j=p.2 ∧ mixedPairAngles θ j q p q=p.1 := by
  simp [mixedPairAngles,hjq]

/-- Only the selected two p-values need to be fixed to keep the full
occupancy constant. All spectator dependence is retained. -/
theorem mixedPairAngles_occupancy {N : ℕ} (f : SelectorFunctions)
    (θ : Fin N → ℝ) (j q : Fin N) (p : ℝ × ℝ)
    (hp : ∀ k,k=j ∨ k=q → f.p (mixedPairAngles θ j q p k)=f.p (θ k)) :
    (fun i => f.p (mixedPairAngles θ j q p i))=(fun i => f.p (θ i)) := by
  funext i
  by_cases hij : i=j
  · exact hp i (Or.inl hij)
  by_cases hiq : i=q
  · exact hp i (Or.inr hiq)
  rw [mixedPairAngles_spectator θ j q i hij hiq]

theorem mixedPairAngles_deformed_spectator {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ)
    (θ : Fin N → ℝ) (j q i : Fin N) (hij : i≠j) (hiq : i≠q) (p : ℝ × ℝ)
    (hp : lam=0 ∨ ∀ k,k=j ∨ k=q → f.p (mixedPairAngles θ j q p k)=f.p (θ k)) :
    deformedPoint f r τ lam (mixedPairAngles θ j q p) i=deformedPoint f r τ lam θ i := by
  rcases hp with rfl | hp
  · simp only [deformedPoint_zero,angleTuple,mixedPairAngles_spectator θ j q i hij hiq]
  · have hP := mixedPairAngles_occupancy f θ j q p hp
    simp only [deformedPoint,retractionShift,hP,mixedPairAngles_spectator θ j q i hij hiq]

/-- During the selected pair integration every unselected branch-volume
factor is exactly constant, including on the coupled Stokes contour. -/
theorem mixedPairAngles_hybrid_volume {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (hj : j∈J) (hq : q∉J) (f : SelectorFunctions) (r τ lam : ℝ)
    (s : ℂ) (θ : Fin N → ℝ) (p : ℝ × ℝ)
    (hp : lam=0 ∨ ∀ k,k=j ∨ k=q → f.p (mixedPairAngles θ j q p k)=f.p (θ k)) :
    mixedHybridVolume J f r τ lam s (mixedPairAngles θ j q p)=
      mixedSourceSlope s (deformedPoint f r τ lam (mixedPairAngles θ j q p) j)*
        ∏ i∈J.erase j,mixedSourceSlope s (deformedPoint f r τ lam θ i) := by
  unfold mixedHybridVolume
  rw [← Finset.mul_prod_erase _ _ hj]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hij : i≠j := (Finset.mem_erase.mp hi).1
  have hiq : i≠q := by intro he; subst i; exact hq (Finset.mem_erase.mp hi).2
  rw [mixedPairAngles_deformed_spectator f r τ lam θ j q i hij hiq p hp]

theorem mixedPairAngles_hybrid_volume_norm {N : ℕ} (J : Finset (Fin N)) (j q : Fin N)
    (hj : j∈J) (hq : q∉J) (f : SelectorFunctions) (r τ lam : ℝ)
    (s : ℂ) (θ : Fin N → ℝ) (p : ℝ × ℝ)
    (hp : lam=0 ∨ ∀ k,k=j ∨ k=q → f.p (mixedPairAngles θ j q p k)=f.p (θ k)) :
    ‖mixedHybridVolume J f r τ lam s (mixedPairAngles θ j q p)‖=
      ‖mixedSourceSlope s (deformedPoint f r τ lam (mixedPairAngles θ j q p) j)‖*
        ∏ i∈J.erase j,‖mixedSourceSlope s (deformedPoint f r τ lam θ i)‖ := by
  rw [mixedPairAngles_hybrid_volume J j q hj hq f r τ lam s θ p hp,norm_mul,norm_prod]

end
end IsingBulk.Tail
