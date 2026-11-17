import IsingBulk.AnisoF002.C03.IsotropicFirstSmoothCoefficient

/-!
# The smooth physical first chart has the unchanged nonzero leading limit

The entire transition annulus is included in dominated convergence.  The
fixed smooth cutoff tends to one after the actual shape scaling; the
majorant is the complete physical Vandermonde rational majorant.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter MeasureTheory IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators

theorem exists_isotropic_first_all_small_smooth_integral_limits {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hhalf : α < Real.pi / 2) (σ : ℂ) (hσ : ‖σ‖ ≤ 1)
    (hres : σ * Complex.exp (-(((n + 1 : ℕ) : ℂ) * ((α : ℂ) * Complex.I))) = 1)
    (j : ℕ) (hbudget : n + 2 * (n + 1).choose 2 < 2 * (j + 1)) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ →
      Tendsto (fun s : ℝ => ∫ q : Fin n → ℝ, isotropicFirstScaledSmooth α σ j r s q)
        (𝓝[>] (0 : ℝ))
        (𝓝 (∫ q : Fin n → ℝ, isotropicFirstLeadingJet α j (flatConstrainedAngles q))) := by
  obtain ⟨δ, C, hδ, hC, hb⟩ := exists_isotropic_first_scaled_jet_majorant
    (Nat.succ_pos n) hα hhalf σ hres j
  have hπ : α < Real.pi := hhalf.trans (by linarith [Real.pi_pos])
  refine ⟨δ / 4, by positivity, ?_⟩
  intro r hr hrδ
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), s ^ 2 < δ / 2 :=
    ((show ContinuousAt (fun s : ℝ => s ^ 2) 0 by fun_prop).eventually
      (Iio_mem_nhds (by simpa using half_pos hδ))).filter_mono nhdsWithin_le_nhds
  apply tendsto_integral_filter_of_dominated_convergence
    (fun q => C * collisionRationalMajorant n (j + 1) q)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact (isotropicFirstScaledSmooth_continuous hα hπ σ hσ j r hs).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin, hsmall] with s hs he
    exact Filter.Eventually.of_forall fun q => by
      by_cases hq : isotropicFirstShapeCutoff r (s • q) = 0
      · rw [isotropicFirstScaledSmooth, hq, zero_mul, norm_zero]
        exact mul_nonneg hC.le (collisionRationalMajorant_nonneg _ _ _)
      · have hshape := isotropicFirstShapeCutoff_support hr (s • q) hq
        have hflat : flatConstrainedAngles (s • q) = fun i => s * flatConstrainedAngles q i :=
          flatConstrainedAngles_mul q s
        have hsq : s ^ 2 + angularQuadratic (fun i => s * flatConstrainedAngles q i) < δ := by
          rw [hflat] at hshape
          linarith
        have hjet := hb s hs (flatConstrainedAngles q) (isotropic_flatConstrainedAngles_sum n q) hsq
        rw [isotropicFirstScaledSmooth, norm_mul]
        apply (mul_le_of_le_one_left (norm_nonneg _) (isotropicFirstShapeCutoff_norm_le_one r (s • q))).trans
        simpa only [collisionRationalMajorant, mul_div_assoc] using hjet
  · exact (collisionRationalMajorant_integrable hbudget).const_mul C
  · exact Filter.Eventually.of_forall fun q => isotropicFirstScaledSmooth_limit hα hπ σ hres hr q j

theorem exists_isotropic_first_all_small_smooth_scaled_limits {n j l : ℕ} {α : ℝ}
    (hα : 0 < α) (hhalf : α < Real.pi / 2) (σ : ℂ) (hσ : ‖σ‖ ≤ 1)
    (hres : σ * Complex.exp (-(((n + 1 : ℕ) : ℂ) * ((α : ℂ) * Complex.I))) = 1)
    (hl : 0 < l) (hdegree : 2 * j + 2 = n + 2 * (n + 1).choose 2 + l) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ →
      Tendsto (fun s : ℝ => (s : ℂ) ^ l *
        iteratedDeriv j (isotropicFirstSmoothCoefficient n α σ r)
          (isotropicRadialParameter α (s ^ 2) - (2 * Real.cos α : ℂ)))
        (𝓝[>] (0 : ℝ)) (𝓝 (isotropicFirstChartAmplitude n α j)) := by
  have hbudget : n + 2 * (n + 1).choose 2 < 2 * (j + 1) := by omega
  obtain ⟨r₀, hr₀, hlim⟩ := exists_isotropic_first_all_small_smooth_integral_limits hα hhalf σ hσ hres j hbudget
  have hπ : α < Real.pi := hhalf.trans (by linarith [Real.pi_pos])
  refine ⟨r₀, hr₀, ?_⟩
  intro r hr hrle
  apply (hlim r hr hrle).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [isotropicFirstSmoothCoefficient_scaled_integral n hα hπ σ hσ j hr hs,
    collision_scaling_ratio_eq (ne_of_gt hs) hdegree]

end
end IsingBulk.AnisoF002.Isotropic
