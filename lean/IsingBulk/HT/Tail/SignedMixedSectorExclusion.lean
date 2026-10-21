import IsingBulk.HT.Tail.SignedMixedSectorIntegralIdentity
import IsingBulk.Tail.MixedSectorExclusion

namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail IsingBulk.HT.Contour Set MeasureTheory Filter Asymptotics
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false

theorem signed_originalSectorIntegral_eq_zero_of_anchor_branch (ζ : ℂ) {N : ℕ} (f : SelectorFunctions)
    (r τ b outer inner : ℝ) (ho : 0<outer) (hi : 0< inner) (hio : inner≤outer/4)
    (q : Fin N) (sigma : Fin N → Fin 3) (hq : sigma q=2) :
    signedOriginalSectorIntegral ζ N f r τ b outer inner ho hi (some (q,sigma))=0 := by
  rw [signedOriginalSectorIntegral_mixed_weight]
  funext s
  simp [originalMixedWeight,nestedSectorWeight_eq_zero_of_anchor_branch b outer inner ho hi hio q sigma hq]

theorem signed_currentSectorIntegral_eq_zero_of_anchor_branch (ζ : ℂ) {N : ℕ} (f : SelectorFunctions)
    (r τ lam b outer inner : ℝ) (ho : 0<outer) (hi : 0< inner) (hio : inner≤outer/4)
    (q qA : Fin N) (sigma : Fin N → Fin 3) (hq : sigma qA=2) :
    signedCurrentSectorIntegral ζ N f r τ lam q b outer inner ho hi (some (qA,sigma))=0 := by
  rw [signedCurrentSectorIntegral_mixed_weight]
  funext s
  simp [currentMixedWeight,nestedSectorWeight_eq_zero_of_anchor_branch b outer inner ho hi hio qA sigma hq]

/-- A current label assigning the named differentiation coordinate to a
true branch vanishes on the entire angular box, at every complex parameter. -/
theorem signed_constructed_current_named_branch_zero (ζ : ℂ) {b η : ℝ} (hb : 0<b) (hbpi : b<Real.pi)
    (hη : 0<η) (hηsmall : η≤Real.sin b/4) :
    ∃ inner₀ : ℝ,0< inner₀ ∧ ∀ (inner : ℝ) (hi : 0< inner),inner≤ inner₀ →
      ∀ α : ℝ,0<α → α<Real.sin b/4 →
      ∀ (N : ℕ) (q qA : Fin N) (sigma : Fin N → Fin 3) (r τ lam outer : ℝ) (ho : 0<outer),
      sigma q=2 → signedCurrentSectorIntegral ζ N (constructedSelector b η α) r τ lam q b outer inner ho hi (some (qA,sigma))=0 := by
  obtain ⟨inner₀,hi₀,hcover⟩ := current_named_sector_nonbranch hb hbpi hη hηsmall
  refine ⟨inner₀,hi₀,?_⟩
  intro inner hi hinner α hα hαsmall N q qA sigma r τ lam outer ho hσq
  rw [signedCurrentSectorIntegral_mixed_weight]
  funext s
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro θ hθ
  by_cases hn : namedSelectorDerivative (constructedSelector b η α) q θ=0
  · simp [currentMixedWeight,hn]
  by_cases hw : nestedSectorWeight b outer inner ho hi qA sigma θ=0
  · simp [currentMixedWeight,hw]
  have hnot := hcover inner hi hinner α hα hαsmall N q θ hθ (subset_closure hn)
  have hB := sector_assignment_tsupport b inner hi sigma
    (tsupport_mul_subset_right (show θ∈tsupport (fun θ => sectorOuterAnchor b outer ho qA θ*
      sectorAssignmentWeight b inner hi sigma θ) from subset_closure hw)) q
  rw [hσq] at hB
  change θ q∈tsupport (sectorBranch b inner hi) at hB
  exact False.elim (hnot hB)

end
end IsingBulk.HT.Tail
