import IsingBulk.AnisoF002.C03.IsotropicPrimeLowerParticles
import IsingBulk.AnisoF002.C03.IsotropicFirstScalingData
import IsingBulk.AnisoF002.C03.RegularIsotropicArithmeticFirst
import IsingBulk.AnisoF002.C03.IsotropicFullSeriesFirstLimit
import IsingBulk.AnisoF002.C03.IsotropicRadialTransfer

/-!
# Complete original isotropic prime-series noncancellation

Every physical particle is present. The actual first coefficient has
its nonzero full amplitude, every lower particle has the proved complete
bound, and every higher same-parity particle is controlled by the complete
differentiated tail. All analytic, deformation and cutoff data have been
constructed internally before these three actual prime-family endpoints.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section

theorem IsotropicFirstArithmeticData.no_actual_radial_germ
    {m K : ℕ} {α phase : ℝ} {σ : ℂ}
    (h : IsotropicFirstArithmeticData m K α phase σ) :
    ¬ HasIsotropicRadialGerm (isotropicFullParticleSeries m phase σ) α := by
  obtain ⟨j, l, hl, hdegree, hret, hA⟩ := h.exists_actual_first_scaling
  obtain ⟨hb0, hbπ, hp, _⟩ := isotropic_first_physical_branch_geometry h.angle_pos h.angle_lt_half
  have hπ : α < Real.pi := by linarith [h.angle_lt_half, Real.pi_pos]
  have hK : 1 ≤ m + 2 * K := by have := h.first_count_ge_seven; omega
  apply actual_complete_series_no_radial_germ_of_first α
    (rightBranchEndpoint (2 * Real.cos α)) ⟨h.angle_pos, hπ⟩ ⟨hb0, hbπ⟩ hp
    m K j l hK hl hret σ h.sign_physical phase h.phase_physical
    (2 * isotropicFirstChartAmplitude (m + 2 * K) α j) hA
    (h.full_first_scaled_limit j l hl hdegree)
  intro k hk
  obtain ⟨δ, A, hδ, _, hbound⟩ := h.actual_lower_particle_bound
    (rightBranchEndpoint (2 * Real.cos α)) ⟨hb0, hbπ⟩ hp j k hk
  exact ⟨δ, A, hδ, hbound⟩

theorem isotropic_positive_prime_no_radial_germ {p a : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (ha : a.Coprime p)
    (hα : 0 < isotropicPrimeAngle p a) (hhalf : isotropicPrimeAngle p a < Real.pi / 2) :
    ¬ HasIsotropicRadialGerm (isotropicFullParticleSeries 0 0 1) (isotropicPrimeAngle p a) :=
  (isotropic_positive_prime_first_arithmetic hp hp7 ha hα hhalf).no_actual_radial_germ

theorem isotropic_even_prime_no_radial_germ {p a : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (ha : a.Coprime p)
    (hα : 0 < isotropicPrimeAngle p a) (hhalf : isotropicPrimeAngle p a < Real.pi / 2) :
    ¬ HasIsotropicRadialGerm (isotropicFullParticleSeries 1 0 1) (isotropicPrimeAngle p a) :=
  (isotropic_even_prime_first_arithmetic hp hp7 ha hα hhalf).no_actual_radial_germ

theorem isotropic_negative_prime_no_radial_germ {p a : ℕ}
    (hp : p.Prime) (hp7 : 7 ≤ p) (ha : a.Coprime p)
    (hα : 0 < Real.pi - isotropicPrimeAngle p a)
    (hhalf : Real.pi - isotropicPrimeAngle p a < Real.pi / 2) :
    ¬ HasIsotropicRadialGerm (isotropicFullParticleSeries 0 Real.pi (-1))
      (Real.pi - isotropicPrimeAngle p a) :=
  (isotropic_negative_prime_first_arithmetic hp hp7 ha hα hhalf).no_actual_radial_germ

end
end IsingBulk.AnisoF002.Isotropic
