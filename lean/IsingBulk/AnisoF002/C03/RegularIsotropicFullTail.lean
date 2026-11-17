import IsingBulk.AnisoF002.C03.RegularIsotropicAnchorCompleteTail
import IsingBulk.AnisoF002.C03.RegularIsotropicMixedCompleteTail
import IsingBulk.AnisoF002.C03.IsotropicRightCompleteTail
import IsingBulk.AnisoF002.C03.IsotropicPhysicalDerivativePartition

/-!
# Summable jets of the complete original isotropic particle coefficients

The actual mixed, right and named-anchor pieces are combined through
the exact full physical derivative partition. All cutoff widths and
the positive deformation are constructed here, before the particle
number and before the derivative order. The resulting statement has
only the original boundary geometry as hypotheses.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set Filter

theorem norm_full_particle_partition_le (x y z : ℂ) :
    ‖x + 2 * (y + z)‖ ≤ ‖x‖ + 2 * (‖y‖ + ‖z‖) := by
  calc
    _ ≤ ‖x‖ + ‖(2 : ℂ) * (y + z)‖ := norm_add_le _ _
    _ = ‖x‖ + 2 * ‖y + z‖ := by rw [norm_mul]; norm_num
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left (norm_add_le y z) (by norm_num))

theorem exists_actual_full_particle_summable_jet_majorants (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ j : ℕ, ∃ M : ℕ → ℝ, (∀ n, 0 ≤ M n) ∧ Summable M ∧
      ∀ n : ℕ, j + 1 ≤ (n + 4).choose 2 →
      ∀ σ : ℂ, σ = 1 ∨ σ = -1 → ∀ a : ℝ, a = 0 ∨ a = Real.pi →
      ∀ ε ∈ Ioo 0 δ,
        ‖iteratedDeriv j (isotropicFullParticleCoefficient (n + 3) a σ)
          (isotropicRadialParameter α ε)‖ ≤ M n * (1 + |Real.log ε|) := by
  obtain ⟨βr, hβr, hβr1, hright⟩ :=
    exists_actual_right_summable_jet_majorants α b hα hb hpoint
  let δB := min (βr / 4) ((Real.pi - b) / 4)
  have hδB : 0 < δB := lt_min (by positivity) (by linarith only [hb.2])
  have hδBr : δB ≤ βr / 4 := min_le_left _ _
  have hδBπ : δB ≤ (Real.pi - b) / 4 := min_le_right _ _
  have hleft : b + δB < Real.pi := by linarith only [hb.2, hδBπ]
  obtain ⟨βa, hβa, _, hanchor⟩ :=
    exists_actual_anchor_summable_jet_majorants α b δB hα hb hpoint hδB hleft
  let ρ := min βa (min (βr / 4) ((Real.pi - b) / 4))
  have hρ : 0 < ρ := lt_min hβa (lt_min (by positivity) (by linarith only [hb.2]))
  have hρa : ρ ≤ βa := min_le_left _ _
  have hρr : ρ ≤ βr / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hρπ : ρ ≤ (Real.pi - b) / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have hcut : RightCutoffGeometry b δB ρ :=
    ⟨hb.1, hδB, hρ, hleft, by linarith only [hρπ, hδBπ, hb.1, Real.pi_pos]⟩
  have hrightB : δB ≤ βr := by linarith only [hδBr, hβr]
  have hrightρ : ρ + δB / 2 ≤ βr := by linarith only [hρr, hδBr, hβr]
  have hsinb : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb.1 hb.2
  have hsinρ : 0 < Real.sin (ρ / 2) := Real.sin_pos_of_pos_of_lt_pi (by positivity)
    (by linarith only [hρπ, hb.1, Real.pi_pos])
  let η := min (Real.sin b / 8) (Real.sin (ρ / 2) / 4)
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hηb : η ≤ Real.sin b / 8 := min_le_left _ _
  have hηρ : η ≤ Real.sin (ρ / 2) / 4 := min_le_right _ _
  have hwidth : 4 * η ≤ Real.sin b := by linarith only [hηb, hsinb]
  have hgap : 2 * η ≤ Real.sin (ρ / 2) := by linarith only [hηρ, hsinρ]
  obtain ⟨δr, hδr, _, hR⟩ := hright η hη hwidth
  obtain ⟨δa, hδa, _, hA⟩ := hanchor ρ hρ hρa hcut η hη hwidth hgap
  obtain ⟨δm, hδm, _, hM⟩ := exists_actual_mixed_summable_jet_majorants α b η hα hb hpoint hη hwidth
  obtain ⟨Δ, hΔ, hpart⟩ := exists_actual_complete_particle_derivative_partition η hη
  let δ := min 1 (min δr (min δa (min δm Δ)))
  have hδ : 0 < δ := lt_min zero_lt_one (lt_min hδr (lt_min hδa (lt_min hδm hΔ)))
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδr' : δ ≤ δr := (min_le_right _ _).trans (min_le_left _ _)
  have hδa' : δ ≤ δa := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hδm' : δ ≤ δm := (((min_le_right _ _).trans (min_le_right _ _)).trans
    (min_le_right _ _)).trans (min_le_left _ _)
  have hδΔ : δ ≤ Δ := (((min_le_right _ _).trans (min_le_right _ _)).trans
    (min_le_right _ _)).trans (min_le_right _ _)
  let τ := δ / 2
  have hτ : 0 < τ := by positivity
  have hτδ : τ ≤ δ := by dsimp [τ]; linarith only [hδ]
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro j
  obtain ⟨Mr, hMr0, hMrs, hMrb⟩ := hR δB ρ hcut hrightB hrightρ j
  obtain ⟨Ma, hMa0, hMas, hMab⟩ := hA j
  obtain ⟨Mm, hMm0, hMms, hMmb⟩ := hM τ hτ (hτδ.trans hδm') j
  let M : ℕ → ℝ := fun n => Mm (n + 3) + 2 * (Mr n + Ma (n + 2))
  have hMs : Summable M :=
    (hMms.comp_injective (fun n m h => Nat.add_right_cancel h)).add
      ((hMrs.add (hMas.comp_injective (fun n m h => Nat.add_right_cancel h))).mul_left 2)
  refine ⟨M, fun n => add_nonneg (hMm0 _) (mul_nonneg (by norm_num) (add_nonneg (hMr0 _) (hMa0 _))), hMs, ?_⟩
  intro n hn σ hσ a ha ε hε
  have hσnorm : ‖σ‖ ≤ 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hrad := isotropicRadialParameter_estimates α ε hα hε.1 (hε.2.le.trans hδ1)
  have he := hpart (n + 2) τ ⟨hτ.le, hτδ.trans hδΔ⟩ b δB ρ a ha σ _ hσnorm hrad.2.2.2.1 j
  have hr := hMrb n hn σ hσ τ ⟨hτ.le, hτδ.trans hδr'⟩ 1 (by norm_num) a ε
    ⟨hε.1, hε.2.trans_le hδr'⟩
  have ham := hMab (n + 2) σ hσnorm τ ⟨hτ.le, hτδ.trans hδa'⟩ a ε
    ⟨hε.1, hε.2.trans_le hδa'⟩
  have hm := hMmb (n + 3) ε hε.1 (hε.2.le.trans hδm') a σ hσnorm
  have ha' := (originalAnchorJetNorm_bounds_complete_sum j (n + 2) η τ b δB ρ a σ
    (isotropicRadialParameter α ε)).trans ham
  have hlog : 1 ≤ 1 + |Real.log ε| := by linarith only [abs_nonneg (Real.log ε)]
  rw [he]
  calc
    _ ≤ ‖iteratedDeriv j (mixedPhysicalCoefficient (n + 3) η τ a σ) (isotropicRadialParameter α ε)‖ +
        2 * (‖iteratedDeriv j (actualWeightedParticleIntegral η τ 1 σ
          (actualLowerRightCutoff η b δB ρ (n + 4)) a) (isotropicRadialParameter α ε)‖ +
          ‖∑ i : Fin (n + 4), iteratedDeriv j (actualWeightedParticleIntegral η τ 1 σ
            (actualLowerAnchorCutoff η b δB ρ i) a) (isotropicRadialParameter α ε)‖) :=
      norm_full_particle_partition_le _ _ _
    _ ≤ Mm (n + 3) + 2 * (Mr n * (1 + |Real.log ε|) + Ma (n + 2)) :=
      add_le_add hm (mul_le_mul_of_nonneg_left (add_le_add hr ha') (by norm_num))
    _ ≤ (Mm (n + 3) + 2 * (Mr n + Ma (n + 2))) * (1 + |Real.log ε|) := by
      have hm' := mul_le_mul_of_nonneg_left hlog (hMm0 (n + 3))
      have ha'' := mul_le_mul_of_nonneg_left hlog (hMa0 (n + 2))
      nlinarith
    _ = _ := rfl

end IsingBulk.AnisoF002.Isotropic
