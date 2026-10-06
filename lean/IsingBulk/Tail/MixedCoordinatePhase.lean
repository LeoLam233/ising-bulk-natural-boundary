import IsingBulk.Tail.MixedCoareaChart
import IsingBulk.Tail.CompactPairCoordinates
import IsingBulk.Tail.PairPhaseInjectivity

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch Set
open scoped BigOperators ContDiff
set_option backward.isDefEq.respectTransparency false

def mixedCoordinatePhase {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ)
    (j q : Fin N) : (Fin N → ℝ) → (Fin N → ℝ) :=
  twoPhaseUpdate (fun x => ∑ i,x i) (fun x => (mixedContourPhaseSum f r τ lam s x).re) j q

def mixedCoordinatePhaseDerivative {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ) (s : ℂ)
    (j q : Fin N) (θ : Fin N → ℝ) : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) :=
  twoPhaseUpdateDeriv (coordinateSumLinear N)
    (Complex.reCLM.comp (fderiv ℝ (mixedContourPhaseSum f r τ lam s) θ)) j q

theorem mixedCoordinatePhase_hasFDerivAt {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (j q : Fin N) (θ : Fin N → ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hW : ∀ i,0<(sourceW s (deformedPoint f r τ lam θ i)).im) :
    HasFDerivAt (mixedCoordinatePhase f r τ lam s j q)
      (mixedCoordinatePhaseDerivative f r τ lam s j q θ) θ := by
  have hF : HasFDerivAt (fun x => ∑ i,x i) (coordinateSumLinear N) θ := by
    have he : (fun x : Fin N → ℝ => ∑ i,x i)=(coordinateSumLinear N : (Fin N → ℝ) → ℝ) := by
      funext x
      exact (coordinateSumLinear_apply x).symm
    rw [he]
    exact (coordinateSumLinear N).hasFDerivAt
  have hG := Complex.reCLM.hasFDerivAt.comp θ
    (mixedContourPhaseSum_spatial_differentiable f hr τ lam s θ hp hm hW).hasFDerivAt
  exact twoPhaseUpdate_hasFDerivAt hF hG j q

theorem mixedPhaseRealDerivative_pair {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (j q : Fin N) (θ : Fin N → ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hplateau : ∀ k,k=j ∨ k=q → deriv f.p (θ k)=0 ∧ deriv f.m (θ k)=0)
    (hW : ∀ i,0<(sourceW s (deformedPoint f r τ lam θ i)).im) :
    (Complex.reCLM.comp (fderiv ℝ (mixedContourPhaseSum f r τ lam s) θ)) (pairDirection j q)=
      (mixedSourceSlope s (deformedPoint f r τ lam θ j)-mixedSourceSlope s (deformedPoint f r τ lam θ q)).re := by
  have hd := mixedContourPhaseSum_spatial_differentiable f hr τ lam s θ hp hm hW
  have hcol (k : Fin N) (hk : k=j ∨ k=q) :
      fderiv ℝ (mixedContourPhaseSum f r τ lam s) θ (Pi.single k 1)=
        mixedSourceSlope s (deformedPoint f r τ lam θ k) := by
    rw [← coordDeriv_eq_fderiv _ _ hd k]
    exact mixedContourPhaseSum_plateau_coordinate f hr τ lam s θ k
      (fun i => hp.differentiable (by simp) _) (fun i => hm.differentiable (by simp) _)
      (hplateau k hk).1 (hplateau k hk).2 hW
  change (fderiv ℝ (mixedContourPhaseSum f r τ lam s) θ (Pi.single j 1-Pi.single q 1)).re=_
  rw [map_sub,hcol j (Or.inl rfl),hcol q (Or.inr rfl)]

theorem mixedCoordinatePhaseDerivative_det {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (j q : Fin N) (hjq : j≠q) (θ : Fin N → ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hplateau : ∀ k,k=j ∨ k=q → deriv f.p (θ k)=0 ∧ deriv f.m (θ k)=0)
    (hW : ∀ i,0<(sourceW s (deformedPoint f r τ lam θ i)).im) :
    (mixedCoordinatePhaseDerivative f r τ lam s j q θ).det=
      -(mixedSourceSlope s (deformedPoint f r τ lam θ j)-mixedSourceSlope s (deformedPoint f r τ lam θ q)).re := by
  rw [mixedCoordinatePhaseDerivative,sumPhaseUpdate_det _ hjq,
    mixedPhaseRealDerivative_pair f hr τ lam s j q θ hp hm hplateau hW]

/-- Global injectivity retains every spectator coordinate. The selected
pair moves along a convex fixed-sum slice of the actual coupled contour. -/
theorem mixedCoordinatePhase_injOn {N : ℕ} (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (j q : Fin N) (hjq : j≠q)
    {S : Set (Fin N → ℝ)} (hSc : Convex ℝ S)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m)
    (hplateau : ∀ θ∈S,∀ k,k=j ∨ k=q → deriv f.p (θ k)=0 ∧ deriv f.m (θ k)=0)
    (hW : ∀ θ∈S,∀ i,0<(sourceW s (deformedPoint f r τ lam θ i)).im)
    (hb : ∀ θ∈S,mixedSourceSlope s (deformedPoint f r τ lam θ j)≠0)
    (hcone : ∀ θ∈S,(2/3:ℝ)*‖mixedSourceSlope s (deformedPoint f r τ lam θ j)‖≤
      (mixedSourceSlope s (deformedPoint f r τ lam θ j)).re)
    (hsep : ∀ θ∈S,‖mixedSourceSlope s (deformedPoint f r τ lam θ q)/
      mixedSourceSlope s (deformedPoint f r τ lam θ j)‖≤(1/4:ℝ)) :
    InjOn (mixedCoordinatePhase f r τ lam s j q) S := by
  intro x hx y hy he
  obtain ⟨hF,hG,hspect⟩ := twoPhaseUpdate_equal_data hjq he
  have hd (θ : Fin N → ℝ) (hθ : θ∈S) := Complex.reCLM.hasFDerivAt.comp θ
    (mixedContourPhaseSum_spatial_differentiable f hr τ lam s θ hp hm (hW θ hθ)).hasFDerivAt
  apply fixed_sum_pair_phase_injective S hSc (fun θ => (mixedContourPhaseSum f r τ lam s θ).re)
    j q hjq (fun θ hθ => (hd θ hθ).differentiableAt) _ hx hy hF hG hspect
  intro θ hθ
  change 0<fderiv ℝ (Complex.reCLM ∘ mixedContourPhaseSum f r τ lam s) θ (pairDirection j q)
  rw [(hd θ hθ).fderiv,mixedPhaseRealDerivative_pair f hr τ lam s j q θ hp hm (hplateau θ hθ) (hW θ hθ)]
  exact (mixed_jacobian_margin (hb θ hθ) (hcone θ hθ) (hsep θ hθ)).2

end
end IsingBulk.Tail
