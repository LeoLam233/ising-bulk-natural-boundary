import IsingBulk.Preferred22.ActualFiniteShell
import IsingBulk.Preferred22.ActualShellTheorem
import IsingBulk.Preferred22.CompleteRightMass

/-! Complete actual right absolute mass above the prime first singular
particle order, combining the distinct finite full-Vandermonde block and
the actual all-order infinite tail on one common source regime. -/
namespace IsingBulk.Preferred22
noncomputable section

/-- Every positive even right transported contribution above Nstar is
included in the genuine absolute sum, with no shell/tail/word premise. -/
theorem preferred_actual_complete_right_mass_tail (d : PreferredBranchData)
    {p : ℕ} (hp : p.Prime) {a : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a)
    (hα : d.alpha=IsingBulk.PrimeFamily.angle p a) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧ ∀ B : PreferredCoareaBump d,B.delta<cap →
      ∃ δ₀ τ₀ ε₀ : ℝ,0<δ₀ ∧ δ₀<B.delta ∧ 0<τ₀ ∧ 0<ε₀ ∧
      ∀ δB τ ε₁ : ℝ,0<δB → δB≤δ₀ → 0≤τ → τ<τ₀ → 0<ε₁ → ε₁≤ε₀ →
      ∀ rcut : ℝ → ℝ,PreferredRightCutoffData d B δB rcut →
      ∀ Nstar k : ℕ,2≤Nstar → Even Nstar → 2*k+2=Nstar^2 →
      PreferredRightAbsoluteMassTail d B τ ε₁ rcut Nstar k := by
  obtain ⟨cs,hcs,hcsa,hs⟩ := preferred_actual_all_diameter_shell_bound d
  obtain ⟨cf,hcf,_hcfa,hf⟩ := preferred_actual_finite_block_shell_bound d hp ha hα
  refine ⟨min cs cf,lt_min hcs hcf,(min_le_left _ _).trans_lt hcsa,?_⟩
  intro B hBcap
  obtain ⟨δs,τs,εs,hδs,hδsδ,hτs,hεs,hq⟩ := hs B (hBcap.trans_le (min_le_left _ _))
  obtain ⟨δf,τf,εf,hδf,_hδfδ,hτf,hεf,hfinite⟩ := hf B (hBcap.trans_le (min_le_right _ _))
  let δ₀ := min δs δf
  let τ₀ := min τs τf
  let ε₀ := min εs εf
  refine ⟨δ₀,τ₀,ε₀,lt_min hδs hδf,(min_le_left _ _).trans_lt hδsδ,
    lt_min hτs hτf,lt_min hεs hεf,?_⟩
  intro δB τ ε₁ hδB hδB₀ hτ hτr hε₁ hε₁₀ rcut hcut Nstar k hNstar hEven hk
  have hq28 := (hq δB hδB (hδB₀.trans (min_le_left _ _)) rcut hcut.2.2.1 hcut.2.2.2.1
    τ hτ (hτr.trans_le (min_le_left _ _)) k).mono_epsilon (hε₁₀.trans (min_le_left _ _))
  have hfb := hfinite δB τ ε₁ hδB (hδB₀.trans (min_le_right _ _)) hτ
    (hτr.trans_le (min_le_right _ _)) hε₁ (hε₁₀.trans (min_le_right _ _)) rcut hcut Nstar k
  exact preferred_complete_right_mass_tail_of_shells d B rcut hcut Nstar k hNstar hEven hk hq28 hfb

end
end IsingBulk.Preferred22
