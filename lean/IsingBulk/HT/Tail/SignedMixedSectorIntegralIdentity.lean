import IsingBulk.HT.Tail.SignedMixedSectorLieIntegral
import IsingBulk.HT.Contour.SignedLeftSectorGaussian

namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail IsingBulk.Lie IsingBulk.HT.Contour Set MeasureTheory Metric Filter
open scoped Topology ContDiff
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem signed_originalSectorIntegral_lie_iterate (ζ : ℂ) {n : ℕ} (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (j q : Fin (n+1)) (sigma : Fin (n+1) → Fin 3)
    {U : Set ℂ}
    (h : SectorLieIntegralIdentity U (mixedContourVelocity (mixedBranchIndexSet sigma) j q f r τ 0)
      (fun z θ => originalMixedWeight f b outer inner ho hi q sigma θ*signedPulledDensity ζ f r τ 0 z θ))
    (k : ℕ) {s : ℂ} (hs : s∈U) :
    iteratedDeriv k (signedOriginalSectorIntegral ζ (n+1) f r τ b outer inner ho hi (some (q,sigma))) s=
      ∫ θ in angleBox (n+1),((lieStep (mixedContourVelocity (mixedBranchIndexSet sigma) j q f r τ 0))^[k]
        (fun z θ => originalMixedWeight f b outer inner ho hi q sigma θ*signedPulledDensity ζ f r τ 0 z θ)) s θ := by
  rw [signedOriginalSectorIntegral_mixed_weight]
  exact h.iteratedDeriv_eq k hs

theorem signed_currentSectorIntegral_lie_iterate (ζ : ℂ) {n : ℕ} (f : SelectorFunctions) (r τ lam b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (j q qA : Fin (n+1)) (sigma : Fin (n+1) → Fin 3)
    {U : Set ℂ}
    (h : SectorLieIntegralIdentity U (mixedContourVelocity (mixedBranchIndexSet sigma) j q f r τ lam)
      (fun z θ => currentMixedWeight f b outer inner ho hi q qA sigma τ θ*signedPulledDensity ζ f r τ lam z θ))
    (k : ℕ) {s : ℂ} (hs : s∈U) :
    iteratedDeriv k (signedCurrentSectorIntegral ζ (n+1) f r τ lam q b outer inner ho hi (some (qA,sigma))) s=
      ∫ θ in angleBox (n+1),((lieStep (mixedContourVelocity (mixedBranchIndexSet sigma) j q f r τ lam))^[k]
        (fun z θ => currentMixedWeight f b outer inner ho hi q qA sigma τ θ*signedPulledDensity ζ f r τ lam z θ)) s θ := by
  rw [signedCurrentSectorIntegral_mixed_weight]
  exact h.iteratedDeriv_eq k hs

end
end IsingBulk.HT.Tail
