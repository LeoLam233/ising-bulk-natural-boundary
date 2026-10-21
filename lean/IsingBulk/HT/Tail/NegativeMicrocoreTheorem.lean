import IsingBulk.Tail.MicrocoreTheorem
import IsingBulk.HT.Tail.NegativeMicrocoreDerivativeBound
import IsingBulk.Tail.MicrocoreSummability
import IsingBulk.Tail.SelectedBranchData

/-! Source-facing nonresonant microcore bound, literal selected family,
fixed cutoff scale before ε,N, and a summable cubic-decay majorant. -/
namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.Tail IsingBulk.HT.Contour
open IsingBulk.Branch IsingBulk.PrimeFamily Filter
open scoped Topology
theorem negative_nonresonant_microcore (d : LocalBranchData)
    (halg : IsAlgebraic ℚ (Complex.exp (-(d.thetaB:ℂ)*Complex.I)))
    (hnot : ∀ N : ℕ, 1 ≤ N → Complex.exp (-(d.thetaB:ℂ)*Complex.I)^N ≠ 1)
    (cap : ℝ) (hcap : 0 < cap) (J : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    ∃ A c E : ℝ, 0 < A ∧ 0 < c ∧ c ≤ 1/4 ∧ c ≤ cap ∧ 0 < E ∧
      Summable (microcoreMajorant A c E) ∧
      ∀ᶠ H : ℝ in atTop, ∀ n : ℕ, ((n+2:ℕ):ℝ) ≤ D*Real.sqrt H →
        let ε := Real.exp (-H)
        let b := microcoreRadius A c (n+2)
        ∀ j ≤ J,
          ‖iteratedDeriv j (negativeOriginalMicrocoreIntegral n d ε b) (radialParameter d.theta ε)‖ ≤
            Real.exp (E*((n+2:ℕ):ℝ)^2)*b^((((n+2:ℕ):ℝ)^2-1)/2) := by
  obtain ⟨A,c,E,hA,hc,hcs,hcap',hE,hbound⟩ := negative_original_microcore_derivative_bound d halg hnot cap hcap J D hD
  refine ⟨A,c,E,hA,hc,hcs,hcap',hE,microcoreMajorant_summable A c E hA.le hc.le (by linarith),?_⟩
  filter_upwards [hbound] with H hH
  intro n hwindow
  dsimp only
  intro j hj
  have hh := hH n hwindow j hj
  rw [microcore_sqrt_power_eq_rpow _ (microcoreRadius_pos A c hc (n+2) (by omega)).le (n+2) (by omega)] at hh
  exact hh

/-- All algebraicity and nonresonance hypotheses are discharged for the
literal FIRST selected prime family; the original radius is sin(theta)/4. -/
theorem negative_selected_nonresonant_microcore {p : ℕ} (hp : p.Prime) {a b : ℤ}
    (ha : Admissible p a) (hb : Admissible p b) (τ α : ℝ) (hτ : 0 < τ) (hα : 0 < α)
    (cap : ℝ) (hcap : 0 < cap) (J : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    let d := selectedLocalBranchData ha hb τ α hτ hα
    ∃ A c E : ℝ, 0 < A ∧ 0 < c ∧ c ≤ 1/4 ∧ c ≤ cap ∧ 0 < E ∧
      Summable (microcoreMajorant A c E) ∧
      ∀ᶠ H : ℝ in atTop, ∀ n : ℕ, ((n+2:ℕ):ℝ) ≤ D*Real.sqrt H →
        let ε := Real.exp (-H)
        let bN := microcoreRadius A c (n+2)
        ∀ j ≤ J,
          ‖iteratedDeriv j (negativeOriginalMicrocoreIntegral n d ε bN) (radialParameter d.theta ε)‖ ≤
            Real.exp (E*((n+2:ℕ):ℝ)^2)*bN^((((n+2:ℕ):ℝ)^2-1)/2) := by
  let d := selectedLocalBranchData ha hb τ α hτ hα
  apply negative_nonresonant_microcore d _ _ cap hcap J D hD
  · exact selectedBranch_algebraic hp ha hb
  · intro N hN he
    apply selectedBranch_not_isOfFinOrder hp ha hb
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨N,by omega,he⟩

end
end IsingBulk.HT.Tail
