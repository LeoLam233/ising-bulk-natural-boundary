import IsingBulk.AnisoF002.C03.IsotropicFirstArithmeticData
import IsingBulk.AnisoF002.C03.RegularIsotropicFiniteAssembly
import IsingBulk.AnisoF002.C03.IsotropicOneParticle

/-!
# Every actual lower particle in the three prime families

The original one-particle integral is included through its exact rational
formula. Every larger lower particle uses all integer constrained means
and the full physical finite-particle estimate. No prefix is discarded.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set
open scoped Topology

theorem exists_actual_one_particle_radial_jet_bound (α phase : ℝ) (σ : ℂ)
    (hα : 0 < α) (hhalf : α < Real.pi / 2)
    (hphase : phase = 0 ∨ phase = Real.pi)
    (hphase_sign : Complex.exp ((phase : ℂ) * Complex.I) = σ) (j : ℕ) :
    ∃ δ A : ℝ, 0 < δ ∧ 0 < A ∧ ∀ ε ∈ Ioo 0 δ,
      ‖iteratedDeriv j (isotropicFullParticleCoefficient 0 phase σ)
        (isotropicRadialParameter α ε)‖ ≤ A := by
  have hπ : α < Real.pi := by linarith [Real.pi_pos]
  rcases hphase with rfl | rfl
  · have hσ : σ = 1 := by simpa only [Complex.ofReal_zero, zero_mul, Complex.exp_zero] using hphase_sign.symm
    clear hphase_sign
    subst σ
    have hcos : Real.cos α < 1 := by
      simpa only [Real.cos_zero] using Real.cos_lt_cos_of_nonneg_of_le_pi
        (x := 0) le_rfl hπ.le hα
    have hne : ((2 * Real.cos α : ℝ) : ℂ) - 2 ≠ 0 := by
      exact_mod_cast (show 2 * Real.cos α - 2 ≠ 0 by linarith)
    apply analytic_upper_extension_radial_jet_bound (G := fun S : ℂ => (S - 2)⁻¹)
      ⟨hα, hπ⟩ (d := 1) zero_lt_one
      ((analyticAt_id.sub analyticAt_const).inv hne) _ j
    intro S _ hS
    exact (isotropic_one_particle_plus hS).symm
  · have hσ : σ = -1 := by simpa only [Complex.exp_pi_mul_I] using hphase_sign.symm
    clear hphase_sign
    subst σ
    have hcos : 0 < Real.cos α :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hhalf⟩
    have hne : ((2 * Real.cos α : ℝ) : ℂ) + 2 ≠ 0 := by
      exact_mod_cast (show 2 * Real.cos α + 2 ≠ 0 by positivity)
    apply analytic_upper_extension_radial_jet_bound (G := fun S : ℂ => (S + 2)⁻¹)
      ⟨hα, hπ⟩ (d := 1) zero_lt_one
      ((analyticAt_id.add analyticAt_const).inv hne) _ j
    intro S _ hS
    exact (isotropic_one_particle_minus hS).symm

theorem IsotropicFirstArithmeticData.actual_lower_particle_bound
    {m K : ℕ} {α phase : ℝ} {σ : ℂ}
    (h : IsotropicFirstArithmeticData m K α phase σ) (b : ℝ)
    (hb : 0 < b ∧ b < Real.pi) (hpoint : 1 + Real.cos b = 2 * Real.cos α)
    (j k : ℕ) (hk : k < K) :
    ∃ δ A : ℝ, 0 < δ ∧ 0 < A ∧ ∀ ε ∈ Ioo 0 δ,
      ‖iteratedDeriv j (isotropicFullParticleCoefficient (m + 2 * k) phase σ)
        (isotropicRadialParameter α ε)‖ ≤ A * (1 + |Real.log ε|) := by
  by_cases hzero : m + 2 * k = 0
  · rw [hzero]
    obtain ⟨δ, A, hδ, hA, hbound⟩ := exists_actual_one_particle_radial_jet_bound
      α phase σ h.angle_pos h.angle_lt_half h.phase_physical h.phase_sign j
    refine ⟨δ, A, hδ, hA, ?_⟩
    intro ε hε
    exact (hbound ε hε).trans (by nlinarith [abs_nonneg (Real.log ε)])
  · let n := m + 2 * k - 1
    have hindex : n + 1 = m + 2 * k := by dsimp [n]; omega
    have hcount : n + 2 = m + 2 * k + 1 := by omega
    have hN0 : ((n + 2 : ℕ) : ℝ) ≠ 0 := by positivity
    have hmean (l : ℤ) : ((n + 2 : ℕ) : ℝ) *
        ((2 * Real.pi * l + phase) / (n + 2 : ℕ)) = 2 * Real.pi * l + phase := by
      field_simp
    have hx1 (l : ℤ) : 2 * Real.cos α -
        Real.cos ((2 * Real.pi * l + phase) / (n + 2 : ℕ)) ≠ 1 :=
      h.all_means_nonbranch (n + 2) (by omega) _ l (hmean l)
    have hden (l : ℤ) : 1 - σ * upperBoundaryRoot
        (2 * Real.cos α - Real.cos ((2 * Real.pi * l + phase) / (n + 2 : ℕ))) ^ (n + 2) ≠ 0 := by
      have hm : ((m + 2 * k + 1 : ℕ) : ℝ) *
          ((2 * Real.pi * l + phase) / (n + 2 : ℕ)) = 2 * Real.pi * l + phase := by
        simpa only [hcount] using hmean l
      simpa only [hcount] using h.lower_nonresonance k hk _ l hm
    simpa only [hindex] using exists_actual_nonresonant_full_particle_bound n j α b phase σ
      h.angle_pos h.angle_lt_half hb hpoint h.phase_physical h.sign_physical hx1 hden

end
end IsingBulk.AnisoF002.Isotropic
