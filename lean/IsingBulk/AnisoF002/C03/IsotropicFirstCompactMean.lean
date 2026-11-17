import IsingBulk.AnisoF002.C03.IsotropicLogarithmicRemainder

/-!
# The full actual first compact mean has the original leading amplitude

The smooth first chart and its entire positive-diameter complement are
recombined through the exact physical all-jet split. The complement
vanishes at the first scale, so the complete mean has the same amplitude.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators

theorem exists_actual_first_compact_mean_scaled_limit (α b : ℝ)
    (hα : 0 < α) (hhalf : α < Real.pi / 2) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) (hαb : α < b) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b →
      2 * η < Real.sin α → ∃ δ : ℝ, 0 < δ ∧ δ ≤ β ∧
      ∀ δB ρB : ℝ, RightCutoffGeometry b δB ρB → δB ≤ β → ρB + δB / 2 ≤ β →
      ∀ n j l : ℕ, 0 < l → 2 * j + 2 = n + 1 + 2 * (n + 2).choose 2 + l →
      ∀ σ : ℂ, σ = 1 ∨ σ = -1 →
        σ * Complex.exp (-(((n + 2 : ℕ) : ℂ) * ((α : ℂ) * Complex.I))) = 1 →
      ∀ τ ∈ Icc 0 δ, ∀ ξ ∈ Icc 0 1,
        Tendsto (fun s : ℝ => (s : ℂ) ^ l *
          iteratedDeriv j (compactMeanPhysicalCoefficient (n + 1) η τ ξ b δB ρB (-α) σ)
            (isotropicRadialParameter α (s ^ 2)))
          (𝓝[>] (0 : ℝ)) (𝓝 (isotropicFirstChartAmplitude (n + 1) α j)) := by
  have hπ : α < Real.pi := hhalf.trans (by linarith [Real.pi_pos])
  obtain ⟨β, hβ, hβ1, haway⟩ := exists_actual_all_particle_compact_mean_away_bound α b ⟨hα, hπ⟩ hb hpoint
  refine ⟨β, hβ, hβ1, ?_⟩
  intro η hη hwidth hηα
  obtain ⟨δ, hδ, hδβ, hab⟩ := haway η hη hwidth
  refine ⟨δ, hδ, hδβ, ?_⟩
  intro δB ρB hcut hδB hρB n j l hl hdegree σ hσ hres τ hτ ξ hξ
  have hσnorm : ‖σ‖ ≤ 1 := by rcases hσ with rfl | rfl <;> simp
  obtain ⟨r₀, hr₀, hnear⟩ := exists_actual_first_near_all_small_scaled_limits
    hα hhalf hη hηα hαb hcut σ hσnorm hres hl hdegree
  let r := r₀ / 2
  have hr : 0 < r := half_pos hr₀
  obtain ⟨A, _, hbound⟩ := hab δB ρB hcut hδB hρB n r hr j
  have haw := radial_logarithmic_remainder_scaled_zero hδ hl
    (hbound σ hσ τ hτ ξ hξ (-α))
  have hlim := (hnear r hr (half_le_self hr₀.le) τ ξ).add haw
  apply (show Tendsto (fun s : ℝ =>
      (s : ℂ) ^ l * iteratedDeriv j (centeredWeightedPhysicalCoefficient η τ ξ (-α) σ
        (weightedCollisionNear r (actualLowerCompactRightCutoff η b δB ρB (n + 2))))
        (isotropicRadialParameter α (s ^ 2)) +
      (s : ℂ) ^ l * iteratedDeriv j (centeredWeightedPhysicalCoefficient η τ ξ (-α) σ
        (weightedCollisionAway r (actualLowerCompactRightCutoff η b δB ρB (n + 2))))
        (isotropicRadialParameter α (s ^ 2)))
      (𝓝[>] (0 : ℝ)) (𝓝 (isotropicFirstChartAmplitude (n + 1) α j)) by
        simpa only [add_zero] using hlim).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  have him := isotropicRadialParameter_im_pos hα hπ (sq_pos_of_pos hs)
  rw [actual_compact_mean_collision_jets hcut (n + 1) η τ ξ (-α) r σ
    hη hτ.1 hξ.1 hσnorm _ him j, mul_add]

end
end IsingBulk.AnisoF002.Isotropic
