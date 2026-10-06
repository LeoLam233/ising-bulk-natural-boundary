import IsingBulk.Tail.MicrocoreVariableCauchy
import IsingBulk.Tail.MicrocoreVariableAnalytic
import IsingBulk.Tail.MicrocoreCauchyCost

/-! Uniform fixed-phase jets of the literal variable factor from the actual
nonresonant gap. Constants precede every N and all derivative orders j≤J. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets

theorem microcore_variable_uniform_exponential_jets (s₀ : ℂ) (c A : ℝ)
    (hs : s₀ ≠ 0) (hS : s₀+s₀⁻¹=(1+c:ℂ)) (hc : |c|<1) (hA : 0 ≤ A) (J : ℕ) :
    ∃ E r : ℝ, 0 < E ∧ 0 < r ∧ ∀ N : ℕ, 1 ≤ N → ∀ s : ℂ, ∀ φ : Fin N → ℂ,
      ‖s-s₀‖ < r → (∀ i, ‖φ i‖ < r) → Real.exp (-A*N)/2 ≤ ‖1-regularYProduct s φ‖ →
      AnalyticAt ℂ microcoreVariableFactor (s,φ) ∧
      JetBound (fun t => microcoreVariableFactor (t,φ)) s J (Real.exp (E*(N:ℝ)^2)) := by
  obtain ⟨Ea,C,rC,hEa,hC,hrC,hbound⟩ := microcore_variable_cauchy_uniform s₀ c hs hS hc
  obtain ⟨rF,hrF,hF⟩ := microcore_variable_uniform_analytic s₀ c hs hS hc
  obtain ⟨E,hE,hcost⟩ := microcore_cauchy_finite_cost hrC hA hC hEa J
  let r := min (rC/2) rF
  have hr : 0 < r := by dsimp [r]; positivity
  refine ⟨E,r,hE,hr,?_⟩
  intro N hN s φ hs' hφ hgap
  have hsrc : ‖s-s₀‖ < rC/2 := hs'.trans_le (min_le_left _ _)
  have hφC : ∀ i, ‖φ i‖ < rC := fun i =>
    (hφ i).trans_le ((min_le_left _ _).trans (half_le_self hrC.le))
  have hpos : 0 < Real.exp (-A*N)/2 := by positivity
  have hne : 1-regularYProduct s φ ≠ 0 := norm_pos_iff.mp (hpos.trans_le hgap)
  have ha := hF N s φ (hs'.trans_le (min_le_right _ _))
    (fun i => (hφ i).trans_le (min_le_right _ _)) hne
  refine ⟨ha,?_,(Real.exp_pos _).le,?_⟩
  · have hh := AnalyticAt.comp (g := microcoreVariableFactor)
      (f := fun t : ℂ => (t,φ)) ha (analyticAt_id.prod analyticAt_const)
    convert! hh using 1
  · intro j hj
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    have hb := hbound N hN φ hφC s hsrc (Real.exp (-A*N)/2) hpos hgap j
    have hrad : microcoreVariableRadius rC (Real.exp (-A*N)/2) C N = microcoreCauchyRadius rC A C N := by
      unfold microcoreVariableRadius microcoreCauchyRadius
      congr 1
      ring
    rw [hrad] at hb
    have he : 2*Real.exp (Ea*(N:ℝ)^2)/(Real.exp (-A*N)/2)=
        4*Real.exp (Ea*(N:ℝ)^2+A*N) := by
      rw [show -A*(N:ℝ)=-(A*N) by ring,Real.exp_neg,Real.exp_add]
      field_simp
      norm_num
    rw [he] at hb
    exact hb.trans (hcost N hN j hj)

end
end IsingBulk.Tail
