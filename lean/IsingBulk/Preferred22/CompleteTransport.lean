import IsingBulk.Preferred22.CompleteRightTransport
import IsingBulk.Preferred22.AnchorRadialIntegral

/-! The exact original all-cell integrated transport obligation, assembled
from the genuine right puncture limit and ordinary named-anchor Stokes.
Both use one physical bump, cutoff, deformation and parameter regime. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set
open scoped BigOperators ContDiff

/-- Every complete source transport cell has the manuscript's exact
integrated derivative identity. The finite collision block and infinite
right tail are included, and all named anchors include N=2 in their own
stronger theorem. No integrated identity or tail estimate is assumed. -/
theorem preferred_actual_complete_transport_integral_identity (d : PreferredBranchData)
    {p : ℕ} (hp : p.Prime) {a : ℤ} (ha : IsingBulk.PrimeFamily.Admissible p a)
    (hα : d.alpha=IsingBulk.PrimeFamily.angle p a) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧ ∀ B : PreferredCoareaBump d,B.delta<cap →
      ∃ δ₀ τ₀ ε₀ : ℝ,0<δ₀ ∧ δ₀<B.delta ∧ 0<τ₀ ∧ 0<ε₀ ∧
      ∀ δB τ ε₁ : ℝ,0<δB → δB≤δ₀ → 0≤τ → τ<τ₀ → 0<ε₁ → ε₁≤ε₀ →
      ∀ rcut : ℝ → ℝ,PreferredRightCutoffData d B δB rcut →
      ∀ Nstar k : ℕ,2≤Nstar → Even Nstar → 2*k+2=Nstar^2 →
      PreferredTransportIntegralIdentity d B.delta τ preferredPopulationCutoff B.p B.m rcut Nstar k ε₁ := by
  obtain ⟨cap,hcap,hcapa,hright⟩ := preferred_actual_complete_right_integral_identity d hp ha hα
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hBcap
  obtain ⟨δ₀,τr,εr,hδ₀,hδ₀δ,hτr,hεr,hr⟩ := hright B hBcap
  obtain ⟨τa,εa,hτa,hεa,hanchor⟩ := preferred_actual_anchor_integral_identity d B
  refine ⟨δ₀,min τr τa,min εr εa,hδ₀,hδ₀δ,lt_min hτr hτa,lt_min hεr hεa,?_⟩
  intro δB τ ε₁ hδB hδB₀ hτ hτ₀ hε₁ hε₁₀ rcut hcut Nstar k hNstar hEvenStar hk
  have hri := hr δB τ ε₁ hδB hδB₀ hτ (hτ₀.trans_le (min_le_left _ _)) hε₁
    (hε₁₀.trans (min_le_left _ _)) rcut hcut Nstar k hNstar hEvenStar hk
  intro n hN hEven j hj ε hε hεr cell
  cases cell with
  | right => exact hri n (by omega) hEven j hj ε hε hεr
  | anchor index =>
    exact hanchor τ hτ (hτ₀.trans_le (min_le_right _ _)) rcut hcut.2.2.1 hcut.2.2.2.1 n index j ε hε
      (hεr.trans_le (hε₁₀.trans (min_le_right _ _)))

end
end IsingBulk.Preferred22
