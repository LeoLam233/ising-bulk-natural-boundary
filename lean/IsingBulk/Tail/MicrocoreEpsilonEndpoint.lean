import IsingBulk.Tail.MicrocoreSourceCutoffs

/-! Epsilon-quantified source endpoint: constants and epsilon0 precede all
particle numbers and all derivative orders in the intermediate window. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch IsingBulk.PrimeFamily Filter

theorem selected_all_branch_microcore_epsilon {p : ℕ} (hp : p.Prime) {a b : ℤ}
    (ha : Admissible p a) (hb : Admissible p b) (τ α : ℝ) (hτ : 0 < τ) (hα : 0 < α)
    (η δ : ℝ) (hδ : 0 < δ) (hδs : δ ≤ 1/2) (J : ℕ) (D : ℝ) (hD : 0 ≤ D) :
    let d := selectedLocalBranchData ha hb τ α hτ hα
    ∃ A c E ε₀ : ℝ, 0 < A ∧ 0 < c ∧ c ≤ 1/4 ∧ c ≤ δ/2 ∧ 0 < E ∧
      0 < ε₀ ∧ ε₀ ≤ 1 ∧ Summable (microcoreMajorant A c E) ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ n : ℕ,
        ((n+2:ℕ):ℝ) ≤ D*Real.sqrt (Real.log (1/ε)) →
        let bN := microcoreRadius A c (n+2)
        ∀ j ≤ J,
          ‖iteratedDeriv j (allBranchMicrocoreIntegral n d η δ hδ ε bN) (radialParameter d.theta ε)‖ ≤
            Real.exp (E*((n+2:ℕ):ℝ)^2)*bN^((((n+2:ℕ):ℝ)^2-1)/2) := by
  let d := selectedLocalBranchData ha hb τ α hτ hα
  obtain ⟨A,c,E,hA,hc,hcs,hcδ,hE,hSum,hbound⟩ :=
    selected_all_branch_microcore hp ha hb τ α hτ hα η δ hδ hδs J D hD
  obtain ⟨H₀,hH⟩ := eventually_atTop.mp hbound
  let ε₀ := Real.exp (-max H₀ 1)
  have hε₀ : 0 < ε₀ := Real.exp_pos _
  have hε₁ : ε₀ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [le_max_right H₀ (1:ℝ)])
  refine ⟨A,c,E,ε₀,hA,hc,hcs,hcδ,hE,hε₀,hε₁,hSum,?_⟩
  intro ε hε hεlt n hwindow
  have hlog : Real.log ε < -max H₀ 1 := by
    have hh := Real.log_lt_log hε hεlt
    rw [Real.log_exp] at hh
    exact hh
  have hH₀ : H₀ ≤ Real.log (1/ε) := by
    rw [one_div,Real.log_inv]
    linarith [le_max_left H₀ (1:ℝ)]
  have he : Real.exp (-Real.log (1/ε))=ε := by
    rw [one_div,Real.log_inv,neg_neg,Real.exp_log hε]
  have hh := hH (Real.log (1/ε)) hH₀ n hwindow
  simpa only [he] using hh

end
end IsingBulk.Tail
