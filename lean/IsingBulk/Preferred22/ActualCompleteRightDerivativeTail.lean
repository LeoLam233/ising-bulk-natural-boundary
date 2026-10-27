import IsingBulk.Preferred22.CompleteRightTransport
import IsingBulk.Preferred22.ActualCompleteRightMass

/-! Actual all-order complex derivative tail for the entire right sector,
including the finite intermediate block. Every quantitative and transport
input is proved from the Preferred source on a common physical regime. -/
namespace IsingBulk.Preferred22
noncomputable section

theorem preferred_actual_complete_right_derivative_tail (d : PreferredBranchData)
    {p : ℕ} (hp : p.Prime) {a : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a)
    (hα : d.alpha=IsingBulk.PrimeFamily.angle p a) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧ ∀ B : PreferredCoareaBump d,B.delta<cap →
      ∃ δ₀ τ₀ ε₀ : ℝ,0<δ₀ ∧ δ₀<B.delta ∧ 0<τ₀ ∧ 0<ε₀ ∧
      ∀ δB τ ε₁ : ℝ,0<δB → δB≤δ₀ → 0≤τ → τ<τ₀ → 0<ε₁ → ε₁≤ε₀ →
      ∀ rcut : ℝ → ℝ,PreferredRightCutoffData d B δB rcut →
      ∀ Nstar k : ℕ,2≤Nstar → Even Nstar → 2*k+2=Nstar^2 →
      PreferredRightDerivativeTailStatement d B τ ε₁ rcut Nstar k := by
  obtain ⟨cm,hcm,hcma,hmass⟩ := preferred_actual_complete_right_mass_tail d hp ha hα
  obtain ⟨ci,hci,_hcia,hidentity⟩ := preferred_actual_complete_right_integral_identity d hp ha hα
  refine ⟨min cm ci,lt_min hcm hci,(min_le_left _ _).trans_lt hcma,?_⟩
  intro B hBcap
  obtain ⟨δm,τm,εm,hδm,hδmB,hτm,hεm,hm⟩ := hmass B (hBcap.trans_le (min_le_left _ _))
  obtain ⟨δi,τi,εi,hδi,_hδiB,hτi,hεi,hi⟩ := hidentity B (hBcap.trans_le (min_le_right _ _))
  refine ⟨min δm δi,min τm τi,min εm εi,lt_min hδm hδi,
    (min_le_left _ _).trans_lt hδmB,lt_min hτm hτi,lt_min hεm hεi,?_⟩
  intro δB τ ε₁ hδB hδB₀ hτ hτr hε₁ hε₁₀ rcut hcut Nstar k hNstar hEven hk
  have hm' := hm δB τ ε₁ hδB (hδB₀.trans (min_le_left _ _)) hτ
    (hτr.trans_le (min_le_left _ _)) hε₁ (hε₁₀.trans (min_le_left _ _)) rcut hcut Nstar k hNstar hEven hk
  have hi' := hi δB τ ε₁ hδB (hδB₀.trans (min_le_right _ _)) hτ
    (hτr.trans_le (min_le_right _ _)) hε₁ (hε₁₀.trans (min_le_right _ _)) rcut hcut Nstar k hNstar hEven hk
  exact preferred_complete_right_derivative_tail_of_mass_identity d B τ ε₁ rcut Nstar k hm' hi'

end
end IsingBulk.Preferred22
