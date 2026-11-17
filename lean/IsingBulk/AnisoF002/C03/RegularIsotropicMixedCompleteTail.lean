import IsingBulk.AnisoF002.C03.RegularIsotropicMixedSummability

/-!
# The complete differentiated physical mixed-population tail

All controls are constructed from the original isotropic boundary
geometry. The full normalized physical coefficients, all constrained
means, both signs and every particle index are included. The proved
rho/N^6 disk and O(N) last-factor loss are explicit in the summable
envelope; no sharper unproved intermediate claim is used.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
open IsingBulk.AnisoF002.RegularTail.C03

theorem exists_actual_mixed_integrated_jet_bound (α b η : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) (hη : 0 < η)
    (hwidth : 4 * η ≤ Real.sin b) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ τ : ℝ, 0 < τ → τ ≤ δ →
      ∃ C g c ρ L : ℝ, 0 < C ∧ 0 < g ∧ 0 < c ∧ 0 < ρ ∧ 0 < L ∧
      ∀ (j n : ℕ), ∀ ε : ℝ, 0 < ε → ε ≤ δ → ∀ a : ℝ, ∀ σ : ℂ, ‖σ‖ ≤ 1 →
        ‖iteratedDeriv j (mixedPhysicalCoefficient n η τ a σ) (isotropicRadialParameter α ε)‖ ≤
          mixedIntegratedEnvelope C g c ρ L j (n + 1) := by
  obtain ⟨δr, hδr, hδr1, hroot⟩ := exists_actual_mixed_root_control α b η hα hb hpoint hη hwidth
  obtain ⟨δb, Cb, hδb, _, hCb, hbody⟩ := exists_positive_period_oneBody_majorant α b hα hb hpoint
  obtain ⟨δd, hδd, _, hdet⟩ := exists_actual_balanced_determinant_bound η
  let δ := min δr (min δb δd)
  have hδ : 0 < δ := lt_min hδr (lt_min hδb hδd)
  have hδr' : δ ≤ δr := min_le_left _ _
  have hδb' : δ ≤ δb := (min_le_right _ _).trans (min_le_left _ _)
  have hδd' : δ ≤ δd := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ, hδ, hδr'.trans hδr1, ?_⟩
  intro τ hτ hτδ
  obtain ⟨d⟩ := hroot τ hτ (hτδ.trans hδr')
  refine ⟨d.pairConstant, d.productGap, d.pairGap, d.radius, 52 * Real.pi * Cb,
    zero_lt_one.trans_le d.pairConstant_ge_one, d.productGap_pos, d.pairGap_pos,
    d.radius_pos, by positivity, ?_⟩
  intro j n ε hε hεδ a σ hσ
  obtain ⟨_, hf0, hfI, hfL, hfb⟩ := hbody η hη hwidth ε hε (hεδ.trans hδb')
  apply d.coefficient_jet_integral_bound n hα hδr1 hη hτ.le hε (hεδ.trans hδr') a hσ
    (fun θ => hdet (n + 1) (by omega) τ 1 ⟨hτ.le, hτδ.trans hδd'⟩ (by norm_num) θ)
    (positivePeriodOneBodyMajorant b Cb ε) hf0 hfI hfL _ j
  intro θ i hi
  rw [actualHomotopyAngle_eq_fixedOccupancy, one_mul]
  exact hfb τ (actualUpperOccupancy η θ) (actualLowerOccupancy η θ)
    ⟨hτ.le, hτδ.trans hδb'⟩ (actualUpperOccupancy_mem_Icc (by omega) η θ)
    (actualLowerOccupancy_mem_Icc (by omega) η θ) (θ i) hi

theorem exists_actual_mixed_summable_jet_majorants (α b η : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) (hη : 0 < η)
    (hwidth : 4 * η ≤ Real.sin b) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ τ : ℝ, 0 < τ → τ ≤ δ →
      ∀ j : ℕ, ∃ M : ℕ → ℝ, (∀ n, 0 ≤ M n) ∧ Summable M ∧
      ∀ (n : ℕ), ∀ ε : ℝ, 0 < ε → ε ≤ δ → ∀ a : ℝ, ∀ σ : ℂ, ‖σ‖ ≤ 1 →
        ‖iteratedDeriv j (mixedPhysicalCoefficient n η τ a σ) (isotropicRadialParameter α ε)‖ ≤ M n := by
  obtain ⟨δ, hδ, hδ1, hbound⟩ := exists_actual_mixed_integrated_jet_bound α b η hα hb hpoint hη hwidth
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro τ hτ hτδ j
  obtain ⟨C, g, c, ρ, L, hC, hg, hc, hρ, hL, hB⟩ := hbound τ hτ hτδ
  refine ⟨fun n => mixedIntegratedEnvelope C g c ρ L j (n + 1),
    fun n => mixedIntegratedEnvelope_nonneg hC.le hg hc hρ hL.le j (n + 1), ?_, ?_⟩
  · exact (mixedIntegratedEnvelope_summable hC.le hg hc hρ hL.le j).comp_injective
      (by intro m n h; dsimp at h; omega)
  · intro n ε hε hεδ a σ hσ
    exact hB j n ε hε hεδ a σ hσ

theorem exists_actual_mixed_complete_differentiated_tail (α b η : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) (hη : 0 < η)
    (hwidth : 4 * η ≤ Real.sin b) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ τ : ℝ, 0 < τ → τ ≤ δ →
      ∀ j : ℕ, ∃ M : ℝ, 0 ≤ M ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ δ → ∀ a : ℝ, ∀ σ : ℂ, ‖σ‖ ≤ 1 →
        Summable (fun n : ℕ =>
          ‖iteratedDeriv j (mixedPhysicalCoefficient n η τ a σ) (isotropicRadialParameter α ε)‖) ∧
        (∑' n : ℕ, ‖iteratedDeriv j (mixedPhysicalCoefficient n η τ a σ)
          (isotropicRadialParameter α ε)‖) ≤ M := by
  obtain ⟨δ, hδ, hδ1, hmajor⟩ := exists_actual_mixed_summable_jet_majorants α b η hα hb hpoint hη hwidth
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro τ hτ hτδ j
  obtain ⟨M, hM0, hMs, hMb⟩ := hmajor τ hτ hτδ j
  refine ⟨∑' n, M n, tsum_nonneg hM0, ?_⟩
  intro ε hε hεδ a σ hσ
  have hb' (n : ℕ) := hMb n ε hε hεδ a σ hσ
  have hs := hMs.of_nonneg_of_le (fun n => norm_nonneg _) hb'
  exact ⟨hs, hs.tsum_le_tsum hb' hMs⟩

theorem exists_actual_mixed_uniform_tail_small (α b η : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) (hη : 0 < η)
    (hwidth : 4 * η ≤ Real.sin b) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ τ : ℝ, 0 < τ → τ ≤ δ →
      ∀ j : ℕ, ∀ e : ℝ, 0 < e → ∃ K : ℕ,
      ∀ ε : ℝ, 0 < ε → ε ≤ δ → ∀ a : ℝ, ∀ σ : ℂ, ‖σ‖ ≤ 1 →
        (∑' n : ℕ, ‖iteratedDeriv j (mixedPhysicalCoefficient (n + K) η τ a σ)
          (isotropicRadialParameter α ε)‖) < e := by
  obtain ⟨δ, hδ, hδ1, hmajor⟩ := exists_actual_mixed_summable_jet_majorants α b η hα hb hpoint hη hwidth
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro τ hτ hτδ j e he
  obtain ⟨M, _, hMs, hMb⟩ := hmajor τ hτ hτδ j
  have ht := (tendsto_sum_nat_add M).eventually (Iio_mem_nhds he)
  obtain ⟨K, hK⟩ := ht.exists
  refine ⟨K, ?_⟩
  intro ε hε hεδ a σ hσ
  have hMshift : Summable (fun n : ℕ => M (n + K)) :=
    hMs.comp_injective (fun n m h => Nat.add_right_cancel h)
  have hb' (n : ℕ) := hMb (n + K) ε hε hεδ a σ hσ
  have hs := hMshift.of_nonneg_of_le (fun n => norm_nonneg _) hb'
  exact (hs.tsum_le_tsum hb' hMshift).trans_lt hK

end
end IsingBulk.AnisoF002.Isotropic
