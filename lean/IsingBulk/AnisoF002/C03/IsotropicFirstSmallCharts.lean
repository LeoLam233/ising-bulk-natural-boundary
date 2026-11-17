import IsingBulk.AnisoF002.C03.IsotropicFirstLocalAsymptotic

/-!
# The same first asymptotic in every sufficiently small actual chart

The chart radius can be chosen after the physical deformation and smooth
partition parameters.  The leading amplitude and original normalization
do not change when the fixed quadratic chart is made smaller.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter MeasureTheory IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators

theorem exists_isotropic_first_all_small_integral_limits {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hhalf : α < Real.pi / 2) (σ : ℂ) (hσ : ‖σ‖ ≤ 1)
    (hres : σ * Complex.exp (-(((n + 1 : ℕ) : ℂ) * ((α : ℂ) * Complex.I))) = 1)
    (j : ℕ) (hbudget : n + 2 * (n + 1).choose 2 < 2 * (j + 1)) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      Tendsto (fun s : ℝ => ∫ q : Fin n → ℝ, isotropicFirstScaledLocal α σ j ρ s q)
        (𝓝[>] (0 : ℝ))
        (𝓝 (∫ q : Fin n → ℝ, isotropicFirstLeadingJet α j (flatConstrainedAngles q))) := by
  obtain ⟨δ, C, hδ, hC, hb⟩ := exists_isotropic_first_scaled_jet_majorant
    (Nat.succ_pos n) hα hhalf σ hres j
  have hπ : α < Real.pi := hhalf.trans (by linarith [Real.pi_pos])
  refine ⟨δ / 2, half_pos hδ, ?_⟩
  intro ρ hρ hρδ
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), s ^ 2 < δ / 2 :=
    ((show ContinuousAt (fun s : ℝ => s ^ 2) 0 by fun_prop).eventually
      (Iio_mem_nhds (by simpa using half_pos hδ))).filter_mono nhdsWithin_le_nhds
  apply tendsto_integral_filter_of_dominated_convergence
    (fun q => C * collisionRationalMajorant n (j + 1) q)
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact (isotropicFirstScaledLocal_measurable hα hπ σ hσ j ρ hs).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin, hsmall] with s hs he
    exact Filter.Eventually.of_forall fun q => by
      by_cases hq : angularQuadratic (flatConstrainedAngles (s • q)) < ρ
      · rw [isotropicFirstScaledLocal, ite_eq_left hq]
        have hflat : flatConstrainedAngles (s • q) = fun i => s * flatConstrainedAngles q i :=
          flatConstrainedAngles_mul q s
        have hsq : s ^ 2 + angularQuadratic (fun i => s * flatConstrainedAngles q i) < δ := by
          rw [hflat] at hq
          linarith
        simpa only [collisionRationalMajorant, mul_div_assoc] using
          hb s hs (flatConstrainedAngles q) (isotropic_flatConstrainedAngles_sum n q) hsq
      · rw [isotropicFirstScaledLocal, ite_eq_right hq, norm_zero]
        exact mul_nonneg hC.le (collisionRationalMajorant_nonneg _ _ _)
  · exact (collisionRationalMajorant_integrable hbudget).const_mul C
  · exact Filter.Eventually.of_forall fun q => isotropicFirstScaledLocal_limit hα hπ σ hres hρ q j

theorem exists_isotropic_first_all_small_scaled_limits {n j l : ℕ} {α : ℝ}
    (hα : 0 < α) (hhalf : α < Real.pi / 2) (σ : ℂ) (hσ : ‖σ‖ ≤ 1)
    (hres : σ * Complex.exp (-(((n + 1 : ℕ) : ℂ) * ((α : ℂ) * Complex.I))) = 1)
    (hl : 0 < l) (hdegree : 2 * j + 2 = n + 2 * (n + 1).choose 2 + l) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      Tendsto (fun s : ℝ => (s : ℂ) ^ l *
        iteratedDeriv j (isotropicFirstLocalCoefficient n α σ ρ)
          (isotropicRadialParameter α (s ^ 2) - (2 * Real.cos α : ℂ)))
        (𝓝[>] (0 : ℝ)) (𝓝 (isotropicFirstChartAmplitude n α j)) := by
  have hbudget : n + 2 * (n + 1).choose 2 < 2 * (j + 1) := by omega
  obtain ⟨ρ₀, hρ₀, hlim⟩ := exists_isotropic_first_all_small_integral_limits hα hhalf σ hσ hres j hbudget
  have hπ : α < Real.pi := hhalf.trans (by linarith [Real.pi_pos])
  refine ⟨ρ₀, hρ₀, ?_⟩
  intro ρ hρ hρle
  apply (hlim ρ hρ hρle).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [isotropicFirstLocalCoefficient_scaled_integral n hα hπ σ hσ j hρ hs,
    collision_scaling_ratio_eq (ne_of_gt hs) hdegree]

end
end IsingBulk.AnisoF002.Isotropic
