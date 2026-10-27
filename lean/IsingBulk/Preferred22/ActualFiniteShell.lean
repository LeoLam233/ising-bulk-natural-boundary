import IsingBulk.Preferred22.ActualVandermondeBounds
import IsingBulk.Preferred22.FiniteShellOfVandermonde

/-! The unconditional finite-block shell bound on the actual source. -/
namespace IsingBulk.Preferred22
noncomputable section

theorem preferred_actual_finite_block_shell_bound (d : PreferredBranchData)
    {p : ℕ} (hp : p.Prime) {a : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a)
    (hα : d.alpha=IsingBulk.PrimeFamily.angle p a) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧ ∀ B : PreferredCoareaBump d,B.delta<cap →
      ∃ δ₀ τ₀ ε₀ : ℝ,0<δ₀ ∧ δ₀<B.delta ∧ 0<τ₀ ∧ 0<ε₀ ∧
      ∀ δB τ ε₁ : ℝ,0<δB → δB≤δ₀ → 0≤τ → τ<τ₀ → 0<ε₁ → ε₁≤ε₀ →
      ∀ rcut : ℝ → ℝ,PreferredRightCutoffData d B δB rcut → ∀ Nstar k : ℕ,
      PreferredFiniteBlockShellBound d B δB τ ε₁ preferredPopulationCutoff rcut Nstar k := by
  exact preferred_finite_block_shell_bound_of_full_vandermonde d hp ha hα
    (preferred_actual_full_vandermonde_bound d)

end
end IsingBulk.Preferred22
