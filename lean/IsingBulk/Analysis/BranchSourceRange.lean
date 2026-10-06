import IsingBulk.Analysis.BranchData

/-! The source range lambda <= epsilon^alpha enters every fixed local current
threshold. All thresholds precede epsilon, occupancy and dimension. -/
namespace IsingBulk.Branch
noncomputable section
open scoped Topology

theorem source_current_range (d : LocalBranchData) (t₀ : ℝ) (ht₀ : 0 < t₀) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε lam ρ : ℝ,
      0 < ε → ε ≤ ε₀ → 0 ≤ lam → lam ≤ ε^d.alpha →
      0 ≤ ρ → ρ ≤ 1 → 0 ≤ lam*ρ ∧ lam*ρ < t₀ := by
  have hc : ContinuousAt (fun ε : ℝ => ε^d.alpha) 0 :=
    (Real.continuous_rpow_const d.alpha_pos.le).continuousAt
  have he := hc.eventually_lt continuousAt_const
    (show (0:ℝ)^d.alpha < t₀ by rw [Real.zero_rpow d.alpha_pos.ne']; exact ht₀)
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨r/2,by positivity,?_⟩
  intro ε lam ρ hε hεr hlam hlampow hρ hρ1
  have heps : ε^d.alpha < t₀ := hball (by
    rw [dist_zero_right,Real.norm_eq_abs,abs_of_pos hε]
    linarith)
  exact ⟨mul_nonneg hlam hρ,
    lt_of_le_of_lt ((mul_le_mul_of_nonneg_left hρ1 hlam).trans (by simpa using hlampow)) heps⟩

theorem source_occupancy_range (d : LocalBranchData) (t₀ : ℝ) (ht₀ : 0 < t₀) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (ε lam P : ℝ) (N : ℕ),
      0 < ε → ε ≤ ε₀ → 0 ≤ lam → lam ≤ ε^d.alpha →
      0 < N → 0 ≤ P → P ≤ N →
      0 ≤ lam*(P/N) ∧ lam*(P/N) < t₀ := by
  obtain ⟨ε₀,hε₀,h⟩ := source_current_range d t₀ ht₀
  refine ⟨ε₀,hε₀,?_⟩
  intro ε lam P N hε hεr hlam hlampow hN hP hPN
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
  exact h ε lam (P/N) hε hεr hlam hlampow (div_nonneg hP hn.le)
    ((div_le_one hn).mpr hPN)

end
end IsingBulk.Branch

