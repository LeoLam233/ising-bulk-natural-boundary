import IsingBulk.AnisoF002.C03.IsotropicFirstCoefficientScaling

/-!
# Nonzero first singularity of the original isotropic local coefficient

The fixed real shape integral is an actual piece of the normalized
physical particle coefficient. Its exact derivatives have the printed
odd s^(-2) and even s^(-1) leading orders along epsilon=s². The full
finite complement and infinite tail are separate remaining integrations.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Filter MeasureTheory IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03
open scoped Topology BigOperators

theorem exists_isotropic_first_local_scaled_limit {n j l : ℕ} {α : ℝ}
    (hα : 0 < α) (hhalf : α < Real.pi / 2) (σ : ℂ) (hσ : ‖σ‖ ≤ 1)
    (hres : σ * Complex.exp (-(((n + 1 : ℕ) : ℂ) * ((α : ℂ) * Complex.I))) = 1)
    (hl : 0 < l) (hdegree : 2 * j + 2 = n + 2 * (n + 1).choose 2 + l) :
    ∃ ρ : ℝ, 0 < ρ ∧
      Tendsto (fun s : ℝ => (s : ℂ) ^ l *
        iteratedDeriv j (isotropicFirstLocalCoefficient n α σ ρ)
          (isotropicRadialParameter α (s ^ 2) - (2 * Real.cos α : ℂ)))
        (𝓝[>] (0 : ℝ)) (𝓝 (isotropicFirstChartAmplitude n α j)) := by
  have hbudget : n + 2 * (n + 1).choose 2 < 2 * (j + 1) := by omega
  obtain ⟨ρ, hρ, hlim⟩ := exists_isotropic_first_local_integral_limit hα hhalf σ hσ hres j hbudget
  have hπ : α < Real.pi := hhalf.trans (by linarith [Real.pi_pos])
  refine ⟨ρ, hρ, ?_⟩
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [isotropicFirstLocalCoefficient_scaled_integral n hα hπ σ hσ j hρ hs,
    collision_scaling_ratio_eq (ne_of_gt hs) hdegree]

theorem exists_isotropic_first_odd_local_nonzero_limit {n : ℕ} (hn0 : 0 < n)
    (hn : Odd (n + 1)) {α : ℝ} (hα : 0 < α) (hhalf : α < Real.pi / 2)
    (σ : ℂ) (hσ : ‖σ‖ ≤ 1)
    (hres : σ * Complex.exp (-(((n + 1 : ℕ) : ℂ) * ((α : ℂ) * Complex.I))) = 1) :
    isotropicFirstChartAmplitude n α (oddTopOrder (n + 1)) ≠ 0 ∧
      ∃ ρ : ℝ, 0 < ρ ∧
        Tendsto (fun s : ℝ => (s : ℂ) ^ 2 *
          iteratedDeriv (oddTopOrder (n + 1)) (isotropicFirstLocalCoefficient n α σ ρ)
            (isotropicRadialParameter α (s ^ 2) - (2 * Real.cos α : ℂ)))
          (𝓝[>] (0 : ℝ)) (𝓝 (isotropicFirstChartAmplitude n α (oddTopOrder (n + 1)))) := by
  exact ⟨isotropicFirstChartAmplitude_odd_ne_zero hn0 hn hα hhalf,
    exists_isotropic_first_local_scaled_limit hα hhalf σ hσ hres
      (by norm_num) (odd_first_scaling_degree hn)⟩

theorem exists_isotropic_first_even_local_nonzero_limit {n : ℕ} (hn : Even (n + 1))
    {α : ℝ} (hα : 0 < α) (hhalf : α < Real.pi / 2) (σ : ℂ) (hσ : ‖σ‖ ≤ 1)
    (hres : σ * Complex.exp (-(((n + 1 : ℕ) : ℂ) * ((α : ℂ) * Complex.I))) = 1) :
    isotropicFirstChartAmplitude n α (evenTopOrder (n + 1)) ≠ 0 ∧
      ∃ ρ : ℝ, 0 < ρ ∧
        Tendsto (fun s : ℝ => (s : ℂ) *
          iteratedDeriv (evenTopOrder (n + 1)) (isotropicFirstLocalCoefficient n α σ ρ)
            (isotropicRadialParameter α (s ^ 2) - (2 * Real.cos α : ℂ)))
          (𝓝[>] (0 : ℝ)) (𝓝 (isotropicFirstChartAmplitude n α (evenTopOrder (n + 1)))) := by
  refine ⟨isotropicFirstChartAmplitude_even_ne_zero hn hα hhalf, ?_⟩
  simpa only [pow_one] using exists_isotropic_first_local_scaled_limit hα hhalf σ hσ hres
    (by norm_num : 0 < 1) (even_first_scaling_degree hn)

end
end IsingBulk.AnisoF002.Isotropic
