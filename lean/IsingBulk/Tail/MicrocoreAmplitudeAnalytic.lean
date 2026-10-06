import IsingBulk.Tail.MicrocoreAmplitudeGrowth

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets

theorem micro_amplitude_uniform_analytic_bound (s₀ : ℂ) (c : ℝ) (hs : s₀ ≠ 0)
    (hS : s₀+s₀⁻¹=(1+c:ℂ)) (hc : |c|<1) :
    ∃ A r : ℝ, 0 < A ∧ 0 < r ∧ ∀ N : ℕ, 1 ≤ N → ∀ s : ℂ, ∀ φ : Fin N → ℂ,
      ‖s-s₀‖ < r → (∀ i, ‖φ i‖ < r) →
      AnalyticAt ℂ (fun z : ℂ × (Fin N → ℂ) => microRegularAmplitude z.1 z.2) (s,φ) ∧
      ‖microRegularAmplitude s φ‖ ≤ Real.exp (A*(N:ℝ)^2) := by
  obtain ⟨C,r,hC,hr,hf⟩ := micro_factor_bounds_uniform s₀ c hs hS hc 0
  obtain ⟨A,hA,hbudget⟩ := microAmplitudeBudget_exp 0 C hC
  refine ⟨A,r,hA,hr,?_⟩
  intro N hN s φ hs' hφ
  have hh := micro_amplitude_jet_product_budget (s,φ) 0 C hC (hf N s φ hs' hφ)
  refine ⟨hh.analytic,?_⟩
  have hn := hh.bound 0 le_rfl
  simp only [norm_iteratedFDeriv_zero] at hn
  exact hn.trans (hbudget N hN)

end
end IsingBulk.Tail
