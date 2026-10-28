import IsingBulk.HT22.Selected.AbsoluteSum

namespace IsingBulk.HT22.Selected
noncomputable section
open IsingBulk.Preferred22
open scoped BigOperators

/-- The same absolute constant controls every fixed upper odd tail N≥5.
The threshold is independent of epsilon; no radial moving cutoff is used. -/
theorem selected_absolute_upper_tail (d : PreferredBranchData) {cap : ℝ} (hcap : 0<cap) :
    ∃ ρ : ℝ, 0<ρ ∧ ρ≤1 ∧ ∀ τ : ℝ, 0<τ → τ<ρ → ∀ j : ℕ,
      ∃ H : ℝ, 0≤H ∧ ∀ negative : Bool, ∀ q : ℕ, 2≤q →
      ∀ ε : ℝ, 0<ε → ε<ρ →
      Summable (fun n : ℕ => ‖iteratedDeriv j (selectedIntegral negative (2*(n+q)) τ
        (cappedCanonicalPreferredBump d cap hcap).p
        (cappedCanonicalPreferredBump d cap hcap).m)
        (IsingBulk.Branch.radialParameter d.alpha ε)‖) ∧
      (∑' n : ℕ, ‖iteratedDeriv j (selectedIntegral negative (2*(n+q)) τ
        (cappedCanonicalPreferredBump d cap hcap).p
        (cappedCanonicalPreferredBump d cap hcap).m)
        (IsingBulk.Branch.radialParameter d.alpha ε)‖)≤H := by
  obtain ⟨ρ,hρ,hρ1,hbound⟩ := selected_absolute_derivative_sum d hcap
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro τ hτ hτρ j
  obtain ⟨H,hH,hHb⟩ := hbound τ hτ hτρ j
  refine ⟨H,hH,?_⟩
  intro negative q hq ε hε hερ
  obtain ⟨r,rfl⟩ : ∃r : ℕ,q=r+2 := ⟨q-2,by omega⟩
  obtain ⟨hs,hb⟩ := hHb negative ε hε hερ
  have hi : Function.Injective (fun n : ℕ => n+r) := by intro a b h;change a+r=b+r at h;omega
  have ht := hs.comp_injective hi
  have hl := tsum_comp_le_tsum_of_inj hs (fun n => norm_nonneg _) hi
  constructor
  · simpa only [Function.comp_def,Nat.add_assoc] using ht
  · simpa only [Function.comp_def,Nat.add_assoc] using hl.trans hb

end
end IsingBulk.HT22.Selected
