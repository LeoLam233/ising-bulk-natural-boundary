import IsingBulk.Tail.MixedSectorLieIntegral
import IsingBulk.Tail.MicrocoreIntegralRegularity

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Lie Set Function
open scoped Topology

theorem real_weighted_lie_iterate_support {n : ℕ}
    (V : ℂ → AngularSpace n → Fin (n+1) → ℂ) (A : ℂ → AngularSpace n → ℂ)
    (w : AngularSpace n → ℝ) (c : ℂ) (k : ℕ) (s : ℂ) :
    support (((lieStep V)^[k] (fun z θ => c*(w θ:ℂ)*A z θ)) s)⊆tsupport w := by
  apply (subset_tsupport _).trans
  apply iterate_lieStep_support_subset V _ isOpen_univ isClosed_closure _ k s (mem_univ _)
  intro z _ θ hθ
  apply subset_tsupport w
  intro hw
  apply hθ
  simp only [hw,Complex.ofReal_zero,mul_zero,zero_mul]

theorem original_mixed_iterate_support {n : ℕ} (f : SelectorFunctions)
    (b outer inner : ℝ) (ho : 0<outer) (hi : 0< inner) (j q : Fin (n+1))
    (sigma : Fin (n+1) → Fin 3) (r τ : ℝ) (k : ℕ) (s : ℂ) :
    support (((lieStep (mixedContourVelocity (mixedBranchIndexSet sigma) j q f r τ 0))^[k]
      (fun z θ => originalMixedWeight f b outer inner ho hi q sigma θ*pulledDensity f r τ 0 z θ)) s)⊆
      tsupport (fun θ => angularSelector f θ*nestedSectorWeight b outer inner ho hi q sigma θ) := by
  have hh := real_weighted_lie_iterate_support
    (mixedContourVelocity (mixedBranchIndexSet sigma) j q f r τ 0) (pulledDensity f r τ 0)
    (fun θ => angularSelector f θ*nestedSectorWeight b outer inner ho hi q sigma θ) 1 k s
  simpa only [one_mul,originalMixedWeight] using hh

theorem current_mixed_iterate_support {n : ℕ} (f : SelectorFunctions)
    (b outer inner : ℝ) (ho : 0<outer) (hi : 0< inner) (j q qA : Fin (n+1))
    (sigma : Fin (n+1) → Fin 3) (r τ lam : ℝ) (k : ℕ) (s : ℂ) :
    support (((lieStep (mixedContourVelocity (mixedBranchIndexSet sigma) j q f r τ lam))^[k]
      (fun z θ => currentMixedWeight f b outer inner ho hi q qA sigma τ θ*pulledDensity f r τ lam z θ)) s)⊆
      tsupport (fun θ => namedSelectorDerivative f q θ*nestedSectorWeight b outer inner ho hi qA sigma θ) :=
  real_weighted_lie_iterate_support
    (mixedContourVelocity (mixedBranchIndexSet sigma) j q f r τ lam) (pulledDensity f r τ lam)
    (fun θ => namedSelectorDerivative f q θ*nestedSectorWeight b outer inner ho hi qA sigma θ)
    (-2*Complex.I*(τ:ℂ)) k s

end
end IsingBulk.Tail
