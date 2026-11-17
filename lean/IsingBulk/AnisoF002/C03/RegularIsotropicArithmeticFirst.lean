import IsingBulk.AnisoF002.C03.RegularIsotropicFirstAssembly
import IsingBulk.AnisoF002.C03.IsotropicFirstArithmeticData

/-!
# Exact arithmetic attachment of the complete first physical coefficient

The original prime-family arithmetic record discharges every discrete
mean condition of the full physical first-particle assembly. The branch
angle is constructed from alpha, with no extra cutoff or analytic data.
-/

noncomputable section
namespace IsingBulk.AnisoF002.Isotropic
open scoped Topology
open Set Filter

namespace IsotropicFirstArithmeticData
variable {m k0 : ℕ} {α phase : ℝ} {σ : ℂ}

theorem full_first_scaled_limit (d : IsotropicFirstArithmeticData m k0 α phase σ)
    (j l : ℕ) (hl : 0 < l)
    (hdegree : 2 * j + 2 = m + 2 * k0 + 2 * (m + 2 * k0 + 1).choose 2 + l) :
    Tendsto (fun s : ℝ => (s : ℂ) ^ l * iteratedDeriv j
      (isotropicFullParticleCoefficient (m + 2 * k0) phase σ) (isotropicRadialParameter α (s ^ 2)))
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * isotropicFirstChartAmplitude (m + 2 * k0) α j)) := by
  let n := m + 2 * k0 - 1
  have hcount := d.first_count_ge_seven
  have hn1 : n + 1 = m + 2 * k0 := by dsimp [n]; omega
  have hn2 : n + 2 = m + 2 * k0 + 1 := by omega
  obtain ⟨hb0, hbπ, hp, _⟩ := isotropic_first_physical_branch_geometry d.angle_pos d.angle_lt_half
  have hdegree' : 2 * j + 2 = n + 1 + 2 * (n + 2).choose 2 + l := by
    simpa only [hn1, hn2] using hdegree
  have hres : σ * Complex.exp (-(((n + 2 : ℕ) : ℂ) * ((α : ℂ) * Complex.I))) = 1 := by
    simpa only [hn2] using d.first_resonance
  have hlift : ∃ k : ℤ, ((n + 2 : ℕ) : ℝ) * (-α) = 2 * Real.pi * k + phase := by
    simpa only [hn2] using d.first_lift
  have hbranch (k : ℤ) :
      2 * Real.cos α - Real.cos ((2 * Real.pi * k + phase) / (n + 2 : ℕ)) ≠ 1 := by
    apply d.all_means_nonbranch (n + 2) (by omega) _ k
    field_simp
  have hclass : ∀ μ ∈ Icc (-Real.pi) Real.pi, ∀ k : ℤ,
      ((n + 2 : ℕ) : ℝ) * μ = 2 * Real.pi * k + phase →
      1 - σ * upperBoundaryRoot (2 * Real.cos α - Real.cos μ) ^ (n + 2) = 0 → μ = α ∨ μ = -α := by
    simpa only [hn2] using d.first_only_centers
  simpa only [hn1] using actual_full_first_particle_scaled_limit n j l α
    (rightBranchEndpoint (2 * Real.cos α)) phase σ d.angle_pos d.angle_lt_half ⟨hb0, hbπ⟩ hp
    hl hdegree' d.phase_physical d.sign_physical hres hlift hbranch hclass

end IsotropicFirstArithmeticData
end IsingBulk.AnisoF002.Isotropic
