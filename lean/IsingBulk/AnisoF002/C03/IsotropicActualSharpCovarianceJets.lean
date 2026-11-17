import IsingBulk.AnisoF002.C03.IsotropicActualSharpCovariance

/-!
# All joint covariance jets at the actual sharp shell scale

The Cauchy constants are independent of the dimension. The protected
disk therefore yields the explicit polynomial N cost and the precise
Delta^{-1-k} factor for every fixed total joint derivative order.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

theorem protectedJetConstant_shell_scaling (k N : ℕ) (c B Δ : ℝ)
    (hN : N ≠ 0) (hΔ : Δ ≠ 0) :
    protectedJetConstant k (c * Δ / (N : ℝ) ^ 2) * (B * (N : ℝ) ^ 2 / Δ) =
      (protectedJetConstant k c * B) * (N : ℝ) ^ (2 * k + 2) / Δ ^ (k + 1) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  have he : c * Δ / (N : ℝ) ^ 2 = c / ((N : ℝ) ^ 2 / Δ) := by field_simp
  rw [he, protectedJetConstant_div k c ((N : ℝ) ^ 2 / Δ) (div_ne_zero (pow_ne_zero 2 hn) hΔ)]
  simp only [div_pow, pow_mul, pow_succ]
  field_simp

/-- The covariance part of frozen F002 `eq:iso-field-jets`, with all
physical coordinate and population hypotheses discharged on the actual
right image. The derivative is the full joint Frechet derivative. -/
theorem exists_actual_right_shell_covariance_all_joint_jets (α b η : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α)
    (hη : 0 < η) (hwidth : 4 * η ≤ Real.sin b) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ k : ℕ, ∃ Ck : ℝ, 0 < Ck ∧
      ∀ (N : ℕ), 0 < N → ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ θ : Fin N → ℝ, (∀ i, θ i ∈ Icc (-b - δ) δ) →
      ∀ r : ℝ, 0 < r → (∀ i j, |θ i - θ j| ≤ 2 * r) → (∃ i j, r ≤ |θ i - θ j|) →
        ‖iteratedFDeriv ℂ k (fun p : ℂ × (Fin N → ℂ) => rightCovarianceField p.1 p.2)
          (actualHomotopyRegularTuple (isotropicRadialParameter α ε) η τ ξ θ)‖ ≤
            Ck * (N : ℝ) ^ (2 * k + 2) / (isotropicShellDelta b ε r θ) ^ (k + 1) := by
  obtain ⟨δ, c, B, hδ, hδ1, hc, hB, hdisks⟩ :=
    exists_actual_right_shell_covariance_disks α b η hα hb hpoint hη hwidth
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro k
  refine ⟨protectedJetConstant k c * B, mul_pos (protectedJetConstant_pos k hc) hB, ?_⟩
  intro N hN ε hε hεδ τ ξ hτ hξ θ hθ r hr hdiam hdiamLower
  have hh := (hdisks N hN ε hε hεδ τ ξ hτ hξ θ hθ r hr hdiam hdiamLower).2 k
  exact hh.trans_eq (protectedJetConstant_shell_scaling k N c B (isotropicShellDelta b ε r θ)
    (Nat.ne_of_gt hN) (isotropicShellDelta_pos b ε r θ hε hr).ne')

end IsingBulk.AnisoF002.Isotropic
