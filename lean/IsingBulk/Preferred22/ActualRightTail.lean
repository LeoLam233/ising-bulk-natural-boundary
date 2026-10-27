import IsingBulk.Preferred22.ActualShellTheorem
import IsingBulk.Preferred22.RightMassTail
import IsingBulk.Preferred22.BumpChoice
import IsingBulk.Preferred22.RightCutoff

/-! Complete large-order absolute sums of the actual transported right
contribution, at every fixed derivative order, with concrete periodic bumps
and cutoff functions. The coefficient transport/Stokes identity and finite
block remain distinct obligations. -/
namespace IsingBulk.Preferred22
noncomputable section
open MeasureTheory
open scoped BigOperators

/-- The actual large-order mass tail on a common, shrinkable source regime.
The bump and exact right cutoff remain parameters, so this composes with
the independently proved integrated-transport identity by taking minima. -/
theorem preferred_actual_large_right_mass_regime (d : PreferredBranchData) :
    ∃ cap : ℝ,0<cap ∧ cap<d.alpha ∧ ∀ B : PreferredCoareaBump d,B.delta<cap →
      ∃ δ₀ τ₀ ε₀ : ℝ,0<δ₀ ∧ δ₀<B.delta ∧ 0<τ₀ ∧ 0<ε₀ ∧
      ∀ δB τ ε₁ : ℝ,0<δB → δB≤δ₀ → 0≤τ → τ<τ₀ → 0<ε₁ → ε₁≤ε₀ →
      ∀ rcut : ℝ → ℝ,PreferredRightCutoffData d B δB rcut →
      ∀ k j : ℕ,j≤k → ∃ A : ℝ,0<A ∧ ∀ ε : ℝ,0<ε → ε<ε₁ →
      Summable (preferredRightLargeMassTerms d B τ rcut k j ε) ∧
      (∑' m,preferredRightLargeMassTerms d B τ rcut k j ε m)≤A*(1+|Real.log ε|) := by
  obtain ⟨cap,hcap,hcapa,hsource⟩ := preferred_actual_all_diameter_shell_bound d
  refine ⟨cap,hcap,hcapa,?_⟩
  intro B hBcap
  obtain ⟨δ₀,τ₀,ε₀,hδ₀,hδ₀δ,hτ₀,hε₀,hq⟩ := hsource B hBcap
  refine ⟨δ₀,τ₀,ε₀,hδ₀,hδ₀δ,hτ₀,hε₀,?_⟩
  intro δB τ ε₁ hδB hδB₀ hτ hτr _hε₁ hε₁₀ rcut hcut k j hj
  have hbound := (hq δB hδB hδB₀ rcut hcut.2.2.1 hcut.2.2.2.1 τ hτ hτr k).mono_epsilon hε₁₀
  exact preferred_complete_right_mass_tail_of_q28 d B rcut hcut k hbound j hj

/-- Unconditional actual complete large-order right mass tail. Every
positive even order above 2k+4 is present in the genuine Summable/tsum result. -/
theorem preferred_actual_all_order_right_mass_tail (d : PreferredBranchData) :
    ∃ B : PreferredCoareaBump d,∃ δB τ₀ ε₀ : ℝ,
      0<δB ∧ δB<B.delta ∧ 0<τ₀ ∧ 0<ε₀ ∧
      PreferredRightCutoffData d B δB (preferredRightCutoff d δB) ∧
      ∀ τ : ℝ,0≤τ → τ<τ₀ → ∀ k j : ℕ,j≤k → ∃ A : ℝ,0<A ∧
      ∀ ε : ℝ,0<ε → ε<ε₀ →
      Summable (preferredRightLargeMassTerms d B τ (preferredRightCutoff d δB) k j ε) ∧
      (∑' m,preferredRightLargeMassTerms d B τ (preferredRightCutoff d δB) k j ε m)≤
        A*(1+|Real.log ε|) := by
  obtain ⟨cap,hcap,_hcapa,hsource⟩ := preferred_actual_all_diameter_shell_bound d
  let B := cappedCanonicalPreferredBump d cap hcap
  have hB : B.delta<cap := cappedCanonicalPreferredBump_delta_lt d hcap
  obtain ⟨δ₀,τ₀,ε₀,hδ₀,hδ₀δ,hτ₀,hε₀,hq⟩ := hsource B hB
  let δB := min δ₀ (preferredRightMargin d B)
  have hδB : 0<δB := lt_min hδ₀ (preferredRightMargin_bounds d B).1
  have hδB₀ : δB≤δ₀ := min_le_left _ _
  have hδBδ : δB<B.delta := hδB₀.trans_lt hδ₀δ
  have hcut := preferred_right_cutoff_data_of_le d B hδB (min_le_right _ _)
  refine ⟨B,δB,τ₀,ε₀,hδB,hδBδ,hτ₀,hε₀,hcut,?_⟩
  intro τ hτ hτr k j hj
  have hbound := hq δB hδB hδB₀ (preferredRightCutoff d δB)
    hcut.2.2.1 hcut.2.2.2.1 τ hτ hτr k
  exact preferred_complete_right_mass_tail_of_q28 d B (preferredRightCutoff d δB) hcut k hbound j hj

end
end IsingBulk.Preferred22
