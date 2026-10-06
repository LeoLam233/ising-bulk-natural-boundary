import IsingBulk.Tail.MixedSectorLieIntegral
import IsingBulk.Tail.SectorIntegralDecomposition

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Lie Set MeasureTheory

theorem originalSectorIntegral_mixed_weight {N : ℕ} (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (q : Fin N) (sigma : Fin N → Fin 3) :
    originalSectorIntegral N f r τ b outer inner ho hi (some (q,sigma))=
      (fun s => ∫ θ in angleBox N,originalMixedWeight f b outer inner ho hi q sigma θ*pulledDensity f r τ 0 s θ) := by
  funext s
  unfold originalSectorIntegral sectorWeightedIntegral
  simp only [sectorPartitionWeight,originalMixedWeight,Complex.ofReal_mul]

theorem currentSectorIntegral_mixed_weight {N : ℕ} (f : SelectorFunctions) (r τ lam b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (q qA : Fin N) (sigma : Fin N → Fin 3) :
    currentSectorIntegral N f r τ lam q b outer inner ho hi (some (qA,sigma))=
      (fun s => ∫ θ in angleBox N,currentMixedWeight f b outer inner ho hi q qA sigma τ θ*pulledDensity f r τ lam s θ) := by
  funext s
  unfold currentSectorIntegral sectorWeightedIntegral
  simp only [sectorPartitionWeight,currentMixedWeight,namedCurrentMultiplier,Complex.ofReal_mul,mul_assoc]

theorem originalSectorIntegral_lie_iterate {n : ℕ} (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (j q : Fin (n+1)) (sigma : Fin (n+1) → Fin 3)
    {U : Set ℂ}
    (h : SectorLieIntegralIdentity U (mixedContourVelocity (mixedBranchIndexSet sigma) j q f r τ 0)
      (fun z θ => originalMixedWeight f b outer inner ho hi q sigma θ*pulledDensity f r τ 0 z θ))
    (k : ℕ) {s : ℂ} (hs : s∈U) :
    iteratedDeriv k (originalSectorIntegral (n+1) f r τ b outer inner ho hi (some (q,sigma))) s=
      ∫ θ in angleBox (n+1),((lieStep (mixedContourVelocity (mixedBranchIndexSet sigma) j q f r τ 0))^[k]
        (fun z θ => originalMixedWeight f b outer inner ho hi q sigma θ*pulledDensity f r τ 0 z θ)) s θ := by
  rw [originalSectorIntegral_mixed_weight]
  exact h.iteratedDeriv_eq k hs

theorem currentSectorIntegral_lie_iterate {n : ℕ} (f : SelectorFunctions) (r τ lam b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (j q qA : Fin (n+1)) (sigma : Fin (n+1) → Fin 3)
    {U : Set ℂ}
    (h : SectorLieIntegralIdentity U (mixedContourVelocity (mixedBranchIndexSet sigma) j q f r τ lam)
      (fun z θ => currentMixedWeight f b outer inner ho hi q qA sigma τ θ*pulledDensity f r τ lam z θ))
    (k : ℕ) {s : ℂ} (hs : s∈U) :
    iteratedDeriv k (currentSectorIntegral (n+1) f r τ lam q b outer inner ho hi (some (qA,sigma))) s=
      ∫ θ in angleBox (n+1),((lieStep (mixedContourVelocity (mixedBranchIndexSet sigma) j q f r τ lam))^[k]
        (fun z θ => currentMixedWeight f b outer inner ho hi q qA sigma τ θ*pulledDensity f r τ lam z θ)) s θ := by
  rw [currentSectorIntegral_mixed_weight]
  exact h.iteratedDeriv_eq k hs

end
end IsingBulk.Tail
