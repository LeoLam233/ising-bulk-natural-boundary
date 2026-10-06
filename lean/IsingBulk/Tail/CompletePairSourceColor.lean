import IsingBulk.Tail.CompletePairIndexedBound
import IsingBulk.Tail.CompactLimitingGeometry
import IsingBulk.Tail.SelectorCutoffs

/-! The actual chord/dispersion three-color assignment, used only in
pointwise absolute estimates. No assigned integral is differentiated. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First

def completePairSourceColor (b η θ : ℝ) : Fin 3 :=
  if lowerChord b θ < η^2/2 then 0 else if 1 ≤ limitingAngularW b θ then 1 else 2

theorem completePairSourceColor_eq_cases {b η θ φ : ℝ}
    (he : completePairSourceColor b η θ=completePairSourceColor b η φ) :
    (lowerChord b θ < η^2/2 ∧ lowerChord b φ < η^2/2) ∨
    (η^2/2 ≤ lowerChord b θ ∧ η^2/2 ≤ lowerChord b φ ∧
      (1 ≤ limitingAngularW b θ ↔ 1 ≤ limitingAngularW b φ)) := by
  unfold completePairSourceColor at he
  split_ifs at he with hθ hφ hθL hφL hφL <;> simp_all
  right
  constructor <;> intro hh <;> linarith

theorem completePairSourceColor_ne_compact {b η θ φ : ℝ}
    (he : completePairSourceColor b η θ ≠ completePairSourceColor b η φ) :
    η^2/2 ≤ lowerChord b θ ∨ η^2/2 ≤ lowerChord b φ := by
  by_contra h
  push Not at h
  exact he (by simp [completePairSourceColor,h.1,h.2])

theorem complete_pair_chord_three_group_bound {N : ℕ} (b η : ℝ)
    (θ : Fin N → ℝ) (z y : Fin N → ℂ) {q σ : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (hhalf : 1/2 ≤ q) (hσ : 0 ≤ σ)
    (hslack : Real.log (1+σ) ≤ -Real.log q/4)
    (hB : ∀ i j, lowerChord b (θ i) < η^2/2 → lowerChord b (θ j) < η^2/2 →
      ‖canceledPair (y i) (y j) (z i) (z j)‖ ≤ 1/2)
    (hC : ∀ i j, η^2/2 ≤ lowerChord b (θ i) → η^2/2 ≤ lowerChord b (θ j) →
      (1 ≤ limitingAngularW b (θ i) ↔ 1 ≤ limitingAngularW b (θ j)) →
      ‖canceledPair (y i) (y j) (z i) (z j)‖ ≤ q)
    (hX : ∀ i j, η^2/2 ≤ lowerChord b (θ i) ∨ η^2/2 ≤ lowerChord b (θ j) →
      ‖canceledPair (y i) (y j) (z i) (z j)‖ ≤ 1+σ) :
    ‖canceledPairProduct z y‖ ≤ (Real.exp (-Real.log q/2))^N*
      Real.exp (-(-Real.log q/12)*(N:ℝ)^2) := by
  apply complete_pair_three_group_bound z y (fun i => completePairSourceColor b η (θ i)) hq hq1 hσ hslack
  · intro i j he
    rcases completePairSourceColor_eq_cases he with hB' | hC'
    · exact (hB i j hB'.1 hB'.2).trans hhalf
    · exact hC i j hC'.1 hC'.2.1 hC'.2.2
  · intro i j he
    exact hX i j (completePairSourceColor_ne_compact he)

end
end IsingBulk.Tail
