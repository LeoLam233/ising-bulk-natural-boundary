import IsingBulk.HT22.Selected.PopulationEstimate

/-! Absolute uniform summation of the actual selected odd tail N≥5, with
constants before the radial parameter and no moving cutoff. -/
namespace IsingBulk.HT22.Selected
noncomputable section
open IsingBulk.Preferred22
open scoped BigOperators

theorem selected_absolute_derivative_sum (d : PreferredBranchData) {cap : ℝ} (hcap : 0<cap) :
    ∃ ρ : ℝ, 0<ρ ∧ ρ≤1 ∧ ∀ τ : ℝ, 0<τ → τ<ρ → ∀ j : ℕ,
      ∃ H : ℝ, 0≤H ∧ ∀ negative : Bool, ∀ ε : ℝ, 0<ε → ε<ρ →
      Summable (fun n : ℕ => ‖iteratedDeriv j (selectedIntegral negative (2*(n+2)) τ
        (cappedCanonicalPreferredBump d cap hcap).p
        (cappedCanonicalPreferredBump d cap hcap).m)
        (IsingBulk.Branch.radialParameter d.alpha ε)‖) ∧
      (∑' n : ℕ, ‖iteratedDeriv j (selectedIntegral negative (2*(n+2)) τ
        (cappedCanonicalPreferredBump d cap hcap).p
        (cappedCanonicalPreferredBump d cap hcap).m)
        (IsingBulk.Branch.radialParameter d.alpha ε)‖)≤H := by
  obtain ⟨ρ,hρ,hρ1,hbound⟩ := selected_population_estimate d hcap
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro τ hτ hτρ j
  obtain ⟨C,hC,hCbound⟩ := hbound τ hτ hτρ j
  let E := fun n : ℕ => C*farOrderEnvelope C (3*j+2) (2*(n+2)+1)
  have he : Summable E :=
    ((farOrderEnvelope_summable hC.le (3*j+2)).comp_injective
      (by intro a b h; change 2*(a+2)+1=2*(b+2)+1 at h; omega : Function.Injective (fun n : ℕ => 2*(n+2)+1))).mul_left C
  have he0 (n : ℕ) : 0≤E n := mul_nonneg hC.le (farOrderEnvelope_nonneg hC.le _ _)
  refine ⟨∑' n,E n,tsum_nonneg he0,?_⟩
  intro negative ε hε hερ
  have hb (n : ℕ) := hCbound negative (n+2) (by omega) ε hε hερ
  have hb' (n : ℕ) : ‖iteratedDeriv j (selectedIntegral negative (2*(n+2)) τ
      (cappedCanonicalPreferredBump d cap hcap).p
      (cappedCanonicalPreferredBump d cap hcap).m)
      (IsingBulk.Branch.radialParameter d.alpha ε)‖≤E n := by
    simpa only [E,farOrderEnvelope,shellOrderEnvelope,Nat.cast_add,Nat.cast_mul,
      Nat.cast_ofNat,Nat.cast_one,mul_assoc] using hb n
  have hf := he.of_nonneg_of_le (fun n => norm_nonneg _) hb'
  exact ⟨hf,hf.tsum_le_tsum hb' he⟩

end
end IsingBulk.HT22.Selected
