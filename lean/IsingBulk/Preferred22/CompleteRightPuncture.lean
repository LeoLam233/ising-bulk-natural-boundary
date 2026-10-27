import IsingBulk.Preferred22.ActualVandermondeBounds
import IsingBulk.Preferred22.RightPunctureOfVandermonde

/-! Complete actual equality-puncture error and flux above the first
singular order, with every finite and infinite source estimate discharged. -/
namespace IsingBulk.Preferred22
noncomputable section

theorem preferred_actual_complete_right_puncture_control (d : PreferredBranchData)
    {p : ℕ} (hp : p.Prime) {a : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a)
    (hα : d.alpha=IsingBulk.PrimeFamily.angle p a) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧ ∀ B : PreferredCoareaBump d,B.delta<cap →
      ∃ δ₀ τ₀ ε₀ : ℝ,0<δ₀ ∧ δ₀<B.delta ∧ 0<τ₀ ∧ 0<ε₀ ∧
      ∀ δB τ ε₁ : ℝ,0<δB → δB≤δ₀ → 0≤τ → τ<τ₀ → 0<ε₁ → ε₁≤ε₀ →
      ∀ rcut : ℝ → ℝ,PreferredRightCutoffData d B δB rcut →
      ∀ Nstar k : ℕ,2≤Nstar → 2*k+2=Nstar^2 →
      ∀ n : ℕ,Nstar+2≤n+1 → Even (n+1) → ∀ j : ℕ,j≤k →
      PreferredRightPunctureValueControl d B τ ε₁ rcut n j ∧
        PreferredRightPunctureFluxControl d B τ ε₁ rcut n j := by
  exact preferred_complete_right_puncture_control_of_vandermonde d hp ha hα
    (preferred_actual_full_vandermonde_bound d)

end
end IsingBulk.Preferred22
