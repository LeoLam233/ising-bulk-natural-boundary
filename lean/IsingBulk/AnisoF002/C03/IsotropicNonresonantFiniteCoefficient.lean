import IsingBulk.AnisoF002.C03.IsotropicRadialExtensionBounds

/-!
# Full fixed-particle compact coefficients at nonresonant means

The genuine near-coincidence continuation controls every ordinary
parameter jet. The exact smooth split and complete positive-diameter
current give the logarithmic bound for the entire actual compact mean.
Every N≥2 is retained, including the small finite competitors.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set
open scoped Topology

theorem exists_actual_nonresonant_compact_mean_bound (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ β ∧
      ∀ δB ρB : ℝ, RightCutoffGeometry b δB ρB → δB ≤ β → ρB + δB / 2 ≤ β →
      ∀ n : ℕ, ∀ τ ∈ Icc 0 δ, ∀ ξ ∈ Icc 0 1, ∀ μ : ℝ,
      ∀ σ : ℂ, σ = 1 ∨ σ = -1 →
        -1 < 2 * Real.cos α - Real.cos μ → 2 * Real.cos α - Real.cos μ ≠ 1 →
        1 - σ * upperBoundaryRoot (2 * Real.cos α - Real.cos μ) ^ (n + 2) ≠ 0 →
      ∀ j : ℕ, ∃ ε₀ A : ℝ, 0 < ε₀ ∧ ε₀ ≤ δ ∧ 0 < A ∧ ∀ ε ∈ Ioo 0 ε₀,
        ‖iteratedDeriv j (compactMeanPhysicalCoefficient (n + 1) η τ ξ b δB ρB μ σ)
          (isotropicRadialParameter α ε)‖ ≤ A * (1 + |Real.log ε|) := by
  obtain ⟨β, hβ, hβ1, haway⟩ := exists_actual_all_particle_compact_mean_away_bound α b hα hb hpoint
  refine ⟨β, hβ, hβ1, ?_⟩
  intro η hη hwidth
  obtain ⟨δ, hδ, hδβ, hbnd⟩ := haway η hη hwidth
  refine ⟨δ, hδ, hδβ, ?_⟩
  intro δB ρB hcut hδB hρB n τ hτ ξ hξ μ σ hσ hx hx1 hden j
  have hσnorm : ‖σ‖ ≤ 1 := by rcases hσ with rfl | rfl <;> simp
  obtain ⟨r₀, hr₀, hnear⟩ := exists_actual_nonresonant_near_jet_bound (n + 1)
    α μ η τ ξ σ hα hη hτ.1 hξ.1 hx hx1 hden
  let r := r₀ / 2
  have hr : 0 < r := half_pos hr₀
  have hrr₀ : r ≤ r₀ := half_le_self hr₀.le
  obtain ⟨εN, A, hεN, hA, hnb⟩ := hnear r hr hrr₀
    (actualLowerCompactRightCutoff η b δB ρB (n + 2))
    (actualLowerCompactRightCutoff_contDiff (k := 0) η b δB ρB (n + 2)).continuous j
  obtain ⟨B, hB, hab⟩ := hbnd δB ρB hcut hδB hρB n r hr j
  let ε₀ := min δ εN
  have hε₀ : 0 < ε₀ := lt_min hδ hεN
  refine ⟨ε₀, A + B, hε₀, min_le_left _ _, by positivity, ?_⟩
  intro ε hε
  have hεδ : ε ∈ Ioo 0 δ := ⟨hε.1, hε.2.trans_le (min_le_left _ _)⟩
  have hε1 : ε ≤ 1 := hεδ.2.le.trans (hδβ.trans hβ1)
  have him := (isotropicRadialParameter_estimates α ε hα hε.1 hε1).2.2.2.1
  rw [actual_compact_mean_collision_jets hcut (n + 1) η τ ξ μ r σ
    hη hτ.1 hξ.1 hσnorm _ him j]
  apply (norm_add_le _ _).trans
  have hnearB := hnb ε ⟨hε.1, hε.2.trans_le (min_le_right _ _)⟩
  have hawayB := hab σ hσ τ hτ ξ hξ μ ε hεδ
  calc
    _ ≤ A + B * (1 + |Real.log ε|) := add_le_add hnearB hawayB
    _ ≤ (A + B) * (1 + |Real.log ε|) := by nlinarith [abs_nonneg (Real.log ε)]

end
end IsingBulk.AnisoF002.Isotropic
