import IsingBulk.HT22.Selected.AbsoluteSum
import IsingBulk.HT22.First.LocalLimit.ThreeParticleSelected.Estimate
namespace IsingBulk.HT22.Selected
noncomputable section
open IsingBulk.Preferred22
open scoped BigOperators

theorem selected_all_odd_bound (d : PreferredBranchData) {cap : ℝ} (hcap : 0<cap) :
    ∃ ρ : ℝ,0<ρ ∧ ρ≤1 ∧ ∀ τ : ℝ,0<τ → τ<ρ → ∀ j : ℕ,
    ∃ C : ℝ,0<C ∧ ∀ negative : Bool,∀ n : ℕ,1≤n → ∀ ε : ℝ,0<ε → ε<ρ →
    ‖iteratedDeriv j (selectedIntegral negative (2*n) τ
      (cappedCanonicalPreferredBump d cap hcap).p (cappedCanonicalPreferredBump d cap hcap).m)
      (IsingBulk.Branch.radialParameter d.alpha ε)‖≤C := by
  obtain ⟨ρA,hρA,hρA1,hA⟩ := selected_absolute_derivative_sum d hcap
  obtain ⟨ρ3,hρ3,_hρ31,h3⟩ := LocalLimit.ThreeParticleSelected.selected_three_particle_estimate d hcap
  refine ⟨min ρA ρ3,lt_min hρA hρ3,(min_le_left _ _).trans hρA1,?_⟩
  intro τ hτ hτρ j
  obtain ⟨CA,hCA,hA⟩ := hA τ hτ (hτρ.trans_le (min_le_left _ _)) j
  obtain ⟨C3,hC3,h3⟩ := h3 τ hτ (hτρ.trans_le (min_le_right _ _)) j
  refine ⟨CA+C3,by positivity,?_⟩
  intro negative n hn ε hε hερ
  by_cases hn1 : n=1
  · subst n
    exact (h3 negative ε hε (hερ.trans_le (min_le_right _ _))).trans (by linarith)
  · obtain ⟨k,rfl⟩ : ∃k : ℕ,n=k+2 := ⟨n-2,by omega⟩
    obtain ⟨hs,hb⟩ := hA negative ε hε (hερ.trans_le (min_le_left _ _))
    exact ((hs.le_tsum k (fun _ _ => norm_nonneg _)).trans hb).trans (by linarith)
end
end IsingBulk.HT22.Selected
