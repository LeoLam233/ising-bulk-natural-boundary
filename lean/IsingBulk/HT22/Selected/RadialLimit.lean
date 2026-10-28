import IsingBulk.HT22.Selected.AbsoluteSum

/-! The entire actual selected high-particle contribution is negligible at
the first inverse-epsilon singularity scale, before any radial limit exchange. -/
namespace IsingBulk.HT22.Selected
noncomputable section
open IsingBulk.Preferred22 Filter
open scoped Topology BigOperators

theorem selected_summed_derivatives_epsilon_zero (d : PreferredBranchData)
    {cap : ℝ} (hcap : 0<cap) :
    ∃ ρ : ℝ, 0<ρ ∧ ρ≤1 ∧ ∀ τ : ℝ, 0<τ → τ<ρ →
      ∀ j : ℕ, ∀ negative : Bool,
      Tendsto (fun ε : ℝ => ε •
        (∑' n : ℕ,iteratedDeriv j (selectedIntegral negative (2*(n+2)) τ
          (cappedCanonicalPreferredBump d cap hcap).p
          (cappedCanonicalPreferredBump d cap hcap).m)
          (IsingBulk.Branch.radialParameter d.alpha ε))) (𝓝[>] 0) (𝓝 (0:ℂ)) := by
  obtain ⟨ρ,hρ,hρ1,hbound⟩ := selected_absolute_derivative_sum d hcap
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro τ hτ hτρ j negative
  obtain ⟨H,_hH,hHbound⟩ := hbound τ hτ hτρ j
  have hbounded : IsBoundedUnder (·≤·) (𝓝[>] (0:ℝ)) (norm ∘
      (fun ε : ℝ => ∑' n : ℕ,iteratedDeriv j (selectedIntegral negative (2*(n+2)) τ
        (cappedCanonicalPreferredBump d cap hcap).p
        (cappedCanonicalPreferredBump d cap hcap).m)
        (IsingBulk.Branch.radialParameter d.alpha ε))) := by
    refine ⟨H,eventually_map.mpr ?_⟩
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hρ).filter_mono nhdsWithin_le_nhds] with ε hε hερ
    obtain ⟨hs,hb⟩ := hHbound negative ε hε hερ
    exact (norm_tsum_le_tsum_norm hs).trans hb
  simpa only [Pi.smul_apply] using!
    NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded
      (tendsto_id.mono_left nhdsWithin_le_nhds) hbounded

end
end IsingBulk.HT22.Selected
