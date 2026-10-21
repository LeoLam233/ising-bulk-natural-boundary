import IsingBulk.Tail.ActualCompactGuardedValues
import IsingBulk.HT.Tail.SignedCompactLieDensity

namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail IsingBulk.Lie IsingBulk.HT.Contour Set Filter MeasureTheory Function
open scoped Topology ContDiff BigOperators
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem signed_compact_guarded_pulled_factorization (σ : ℂ) (hσ : ‖σ‖ = 1) {n : ℕ}
    (f : SelectorFunctions) (hf : RegularSelector f) {r τ lam h : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (hτ : 0 ≤ τ) (hlam : 0 ≤ lam) (hh : 0 < h)
    (P : Finset (Fin (n+1) × Fin (n+1))) (M : ℕ) {i j : Fin (n+1)} (hij : (i,j) ∈ P)
    (w : AngularSpace n → ℂ) (hw : ContDiff ℝ ∞ w) (k : ℕ)
    {s : ℂ} {θ : AngularSpace n} (hp : (s,θ) ∈ compactSelectedDomain f r τ lam i j) :
    ((lieStep (currentSelectedPairField f r τ lam i j))^[k]
      (fun z x => compactGuardedWeight P M h i j w x*signedPulledDensity σ f r τ lam z x)) s θ=
      signedMixedSimpleKernel σ f r τ lam s θ*
        ((lieStep (currentSelectedPairField f r τ lam i j))^[k]
          (fun z x => (compactGuardedPairWeight P M h i j x:ℂ)*(w x*compactRegularDensity f r τ lam z x))) s θ := by
  have he := signed_compact_selected_density_all_order σ hσ f hf hr hr1 hτ hlam i j
    (compactGuardedWeight P M h i j w)
    (ParameterSmoothOn.angular _ _ (compactGuardedWeight_smooth P M hh hij w hw)) k hp
  have hfun : (fun z x => compactGuardedWeight P M h i j w x*compactRegularDensity f r τ lam z x)=
      (fun z x => (compactGuardedPairWeight P M h i j x:ℂ)*(w x*compactRegularDensity f r τ lam z x)) := by
    funext z x
    unfold compactGuardedWeight
    ring
  rwa [hfun] at he

end
end IsingBulk.HT.Tail
