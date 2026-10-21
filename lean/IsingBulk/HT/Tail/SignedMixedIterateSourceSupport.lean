import IsingBulk.Tail.MixedIterateSourceSupport
import IsingBulk.HT.Tail.SignedMixedSectorLieIntegral

namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail IsingBulk.Lie IsingBulk.HT.Contour Set MeasureTheory Metric Filter Function
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem signed_original_mixed_iterate_support (ζ : ℂ) {n : ℕ} (f : SelectorFunctions)
    (b outer inner : ℝ) (ho : 0<outer) (hi : 0< inner) (j q : Fin (n+1))
    (sigma : Fin (n+1) → Fin 3) (r τ : ℝ) (k : ℕ) (s : ℂ) :
    support (((lieStep (mixedContourVelocity (mixedBranchIndexSet sigma) j q f r τ 0))^[k]
      (fun z θ => originalMixedWeight f b outer inner ho hi q sigma θ*signedPulledDensity ζ f r τ 0 z θ)) s)⊆
      tsupport (fun θ => angularSelector f θ*nestedSectorWeight b outer inner ho hi q sigma θ) := by
  have hh := real_weighted_lie_iterate_support
    (mixedContourVelocity (mixedBranchIndexSet sigma) j q f r τ 0) (signedPulledDensity ζ f r τ 0)
    (fun θ => angularSelector f θ*nestedSectorWeight b outer inner ho hi q sigma θ) 1 k s
  simpa only [one_mul,originalMixedWeight] using hh

theorem signed_current_mixed_iterate_support (ζ : ℂ) {n : ℕ} (f : SelectorFunctions)
    (b outer inner : ℝ) (ho : 0<outer) (hi : 0< inner) (j q qA : Fin (n+1))
    (sigma : Fin (n+1) → Fin 3) (r τ lam : ℝ) (k : ℕ) (s : ℂ) :
    support (((lieStep (mixedContourVelocity (mixedBranchIndexSet sigma) j q f r τ lam))^[k]
      (fun z θ => currentMixedWeight f b outer inner ho hi q qA sigma τ θ*signedPulledDensity ζ f r τ lam z θ)) s)⊆
      tsupport (fun θ => namedSelectorDerivative f q θ*nestedSectorWeight b outer inner ho hi qA sigma θ) :=
  real_weighted_lie_iterate_support
    (mixedContourVelocity (mixedBranchIndexSet sigma) j q f r τ lam) (signedPulledDensity ζ f r τ lam)
    (fun θ => namedSelectorDerivative f q θ*nestedSectorWeight b outer inner ho hi qA sigma θ)
    (-2*Complex.I*(τ:ℂ)) k s

end
end IsingBulk.HT.Tail
