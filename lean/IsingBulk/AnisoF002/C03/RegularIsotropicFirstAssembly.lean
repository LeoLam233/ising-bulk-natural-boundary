import IsingBulk.AnisoF002.C03.RegularIsotropicFiniteAssembly

/-!
# The complete first physical particle has twice the genuine first amplitude

The exact lower compact-mean set contains the negative first mean and
excludes the positive one. Every other actual integer mean is controlled
by its genuine nonresonant bound. The mixed and all named-anchor terms
vanish after scaling. The factor two is exactly the checked reflection
factor in the complete physical partition.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology BigOperators
open Set Filter

namespace ActualFinitePartitionControl
variable {α b : ℝ} (c : ActualFinitePartitionControl α b)

theorem first_lift_mem (n : ℕ) (phase : ℝ) (k₀ : ℤ) (hα : 0 < α) (hαb : α < b)
    (hlift : ((n + 2 : ℕ) : ℝ) * (-α) = 2 * Real.pi * k₀ + phase) :
    k₀ ∈ admissibleRightLifts (n + 2) b c.buffer phase := by
  apply (admissibleRightLifts_mem_iff _ _ _ _ _).2
  rw [← hlift]
  have hN : (0 : ℝ) ≤ (n + 2 : ℕ) := by positivity
  constructor
  · exact mul_le_mul_of_nonneg_left (by linarith only [hαb, c.buffer_pos]) hN
  · exact mul_le_mul_of_nonneg_left (by linarith only [hα, c.buffer_pos]) hN

theorem first_lift_mean (n : ℕ) (phase : ℝ) (k₀ : ℤ)
    (hlift : ((n + 2 : ℕ) : ℝ) * (-α) = 2 * Real.pi * k₀ + phase) :
    constrainedRightMean (n + 2) b phase k₀ - b = -α := by
  simp only [constrainedRightMean, add_sub_cancel_left]
  apply (div_eq_iff (by positivity : ((n + 2 : ℕ) : ℝ) ≠ 0)).2
  linarith only [hlift]

theorem other_first_means_nonresonant (n : ℕ) (phase : ℝ) (σ : ℂ) (k₀ : ℤ)
    (hlift : ((n + 2 : ℕ) : ℝ) * (-α) = 2 * Real.pi * k₀ + phase)
    (hclass : ∀ μ ∈ Icc (-Real.pi) Real.pi, ∀ k : ℤ,
      ((n + 2 : ℕ) : ℝ) * μ = 2 * Real.pi * k + phase →
      1 - σ * upperBoundaryRoot (2 * Real.cos α - Real.cos μ) ^ (n + 2) = 0 →
        μ = α ∨ μ = -α) :
    ∀ k ∈ (admissibleRightLifts (n + 2) b c.buffer phase).erase k₀,
      1 - σ * upperBoundaryRoot
        (2 * Real.cos α - Real.cos (constrainedRightMean (n + 2) b phase k - b)) ^ (n + 2) ≠ 0 := by
  intro k hk hz
  have hkm := Finset.mem_of_mem_erase hk
  have hkne := Finset.ne_of_mem_erase hk
  have hmean := c.admissible_mean_bounds n phase k hkm
  have hm : ((n + 2 : ℕ) : ℝ) * (constrainedRightMean (n + 2) b phase k - b) =
      2 * Real.pi * k + phase := by
    simp only [constrainedRightMean, add_sub_cancel_left]
    field_simp
  rcases hclass _ ⟨hmean.1.1.le, hmean.1.2.le⟩ k hm hz with hpos | hneg
  · linarith only [hmean.2, hpos]
  · exact hkne (constrainedRightMean_lift_injective (by omega : 0 < n + 2) b phase
      (hneg.trans (first_lift_mean (b := b) n phase k₀ hlift).symm))

include c in
theorem full_first_particle_scaled_limit (n j l : ℕ)
    (hα : 0 < α) (hhalf : α < Real.pi / 2) (hαb : α < b)
    (hl : 0 < l) (hdegree : 2 * j + 2 = n + 1 + 2 * (n + 2).choose 2 + l)
    (phase : ℝ) (hphase : phase = 0 ∨ phase = Real.pi)
    (σ : ℂ) (hσ : σ = 1 ∨ σ = -1)
    (hres : σ * Complex.exp (-(((n + 2 : ℕ) : ℂ) * ((α : ℂ) * Complex.I))) = 1)
    (k₀ : ℤ) (hlift : ((n + 2 : ℕ) : ℝ) * (-α) = 2 * Real.pi * k₀ + phase)
    (hx1 : ∀ k : ℤ, 2 * Real.cos α - Real.cos ((2 * Real.pi * k + phase) / (n + 2 : ℕ)) ≠ 1)
    (hclass : ∀ μ ∈ Icc (-Real.pi) Real.pi, ∀ k : ℤ,
      ((n + 2 : ℕ) : ℝ) * μ = 2 * Real.pi * k + phase →
      1 - σ * upperBoundaryRoot (2 * Real.cos α - Real.cos μ) ^ (n + 2) = 0 →
        μ = α ∨ μ = -α) :
    Tendsto (fun s : ℝ => (s : ℂ) ^ l * iteratedDeriv j
      (isotropicFullParticleCoefficient (n + 1) phase σ) (isotropicRadialParameter α (s ^ 2)))
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * isotropicFirstChartAmplitude (n + 1) α j)) := by
  have hσnorm : ‖σ‖ ≤ 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hk₀ := c.first_lift_mem n phase k₀ hα hαb hlift
  have hmean₀ := first_lift_mean (b := b) n phase k₀ hlift
  obtain ⟨A, hA, hreg⟩ := c.regularJetRemainder_bound n j phase σ hσnorm
  have hreg0 := radial_logarithmic_remainder_scaled_zero c.radius_pos hl
    (fun ε hε => (hreg ε hε).trans (by nlinarith [abs_nonneg (Real.log ε)] :
      A ≤ A * (1 + |Real.log ε|)))
  have hother := c.other_first_means_nonresonant n phase σ k₀ hlift hclass
  obtain ⟨e, B, he, _, hmeans⟩ := c.nonresonant_means_log_bound n j phase σ hσ
    ((admissibleRightLifts (n + 2) b c.buffer phase).erase k₀)
    (fun k _ => isotropic_boundary_dispersion_gt_neg_one hα hhalf _)
    (fun k _ => by simpa only [constrainedRightMean, add_sub_cancel_left] using hx1 k) hother
  have hmeans0 := radial_logarithmic_remainder_scaled_zero he hl hmeans
  have hfirst : Tendsto (fun s : ℝ => (s : ℂ) ^ l * c.meanJet n j phase σ k₀ (s ^ 2))
      (𝓝[>] (0 : ℝ)) (𝓝 (isotropicFirstChartAmplitude (n + 1) α j)) := by
    simpa only [meanJet, hmean₀] using c.first_limit n j l hl hdegree σ hσ hres
  have hlim : Tendsto (fun s : ℝ => (s : ℂ) ^ l * c.regularJetRemainder n j phase σ (s ^ 2) +
      2 * ((s : ℂ) ^ l * c.meanJet n j phase σ k₀ (s ^ 2) +
        (s : ℂ) ^ l * ∑ k ∈ (admissibleRightLifts (n + 2) b c.buffer phase).erase k₀,
          c.meanJet n j phase σ k (s ^ 2))) (𝓝[>] (0 : ℝ))
      (𝓝 (2 * isotropicFirstChartAmplitude (n + 1) α j)) := by
    simpa only [zero_add, add_zero] using hreg0.add (tendsto_const_nhds.mul (hfirst.add hmeans0))
  apply hlim.congr'
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), s ^ 2 < c.radius :=
    ((show ContinuousAt (fun s : ℝ => s ^ 2) 0 by fun_prop).eventually
      (Iio_mem_nhds (by simpa using c.radius_pos))).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with s hs hsd
  rw [c.partition_jets n j phase hphase σ hσ (s ^ 2) ⟨sq_pos_of_pos hs, hsd⟩,
    ← Finset.sum_erase_add (s := admissibleRightLifts (n + 2) b c.buffer phase)
      (f := fun k => c.meanJet n j phase σ k (s ^ 2)) hk₀]
  ring

end ActualFinitePartitionControl

theorem actual_full_first_particle_scaled_limit (n j l : ℕ) (α b phase : ℝ) (σ : ℂ)
    (hα : 0 < α) (hhalf : α < Real.pi / 2) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α)
    (hl : 0 < l) (hdegree : 2 * j + 2 = n + 1 + 2 * (n + 2).choose 2 + l)
    (hphase : phase = 0 ∨ phase = Real.pi) (hσ : σ = 1 ∨ σ = -1)
    (hres : σ * Complex.exp (-(((n + 2 : ℕ) : ℂ) * ((α : ℂ) * Complex.I))) = 1)
    (hlift : ∃ k₀ : ℤ, ((n + 2 : ℕ) : ℝ) * (-α) = 2 * Real.pi * k₀ + phase)
    (hx1 : ∀ k : ℤ, 2 * Real.cos α - Real.cos ((2 * Real.pi * k + phase) / (n + 2 : ℕ)) ≠ 1)
    (hclass : ∀ μ ∈ Icc (-Real.pi) Real.pi, ∀ k : ℤ,
      ((n + 2 : ℕ) : ℝ) * μ = 2 * Real.pi * k + phase →
      1 - σ * upperBoundaryRoot (2 * Real.cos α - Real.cos μ) ^ (n + 2) = 0 →
        μ = α ∨ μ = -α) :
    Tendsto (fun s : ℝ => (s : ℂ) ^ l * iteratedDeriv j
      (isotropicFullParticleCoefficient (n + 1) phase σ) (isotropicRadialParameter α (s ^ 2)))
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * isotropicFirstChartAmplitude (n + 1) α j)) := by
  obtain ⟨c⟩ := exists_actual_finite_partition_control α b hα hhalf hb hpoint
  obtain ⟨k₀, hk₀⟩ := hlift
  exact c.full_first_particle_scaled_limit n j l hα hhalf
    (isotropic_first_angle_lt_branch ⟨hα, hhalf.trans (by linarith only [Real.pi_pos])⟩ hb hpoint)
    hl hdegree phase hphase σ hσ hres k₀ hk₀ hx1 hclass

end IsingBulk.AnisoF002.Isotropic
