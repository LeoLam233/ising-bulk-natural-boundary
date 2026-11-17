import IsingBulk.AnisoF002.C03.IsotropicCompleteShellCoarea

/-!
# The exact physical signed shell bound at the frozen Delta scale

The full root product is restored literally, for either physical sign.
For N at least three the complete shell estimate has precisely the
power Delta^(N-3), with one fixed exponential constant and N cubed.
The preceding raw estimate also retains the N=2 case.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric MeasureTheory

def actualSignedFullDensity {N : ℕ} (s σ : ℂ) (η τ ξ : ℝ) (θ : Fin N → ℝ) : ℝ :=
  (∏ k, ‖1 + actualPhaseSlope s η τ ξ θ k‖) /
    ‖1 - σ * ∏ k, isotropicInteriorRoot (s, actualHomotopyAngle η τ ξ θ k)‖

theorem actualFullPhaseDensity_zero_eq_signed {N : ℕ} (s : ℂ) (η τ ξ : ℝ) (θ : Fin N → ℝ) :
    actualFullPhaseDensity s η τ ξ 0 θ = actualSignedFullDensity s 1 η τ ξ θ := by
  unfold actualFullPhaseDensity actualSignedFullDensity
  rw [Complex.ofReal_zero, sub_zero, one_mul]
  rw [show -Complex.I * actualTotalPhase η τ ξ (s, θ) =
    -(actualTotalPhase η τ ξ (s, θ) * Complex.I) by ring, actualTotalPhase_exp_product]

theorem actualFullPhaseDensity_pi_eq_signed {N : ℕ} (s : ℂ) (η τ ξ : ℝ) (θ : Fin N → ℝ) :
    actualFullPhaseDensity s η τ ξ Real.pi θ = actualSignedFullDensity s (-1) η τ ξ θ := by
  unfold actualFullPhaseDensity actualSignedFullDensity
  rw [phase_exp_pi_shift, actualTotalPhase_exp_product, neg_one_mul]

theorem exists_actual_complete_signed_shell_coarea (α b η : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α)
    (hη : 0 < η) (hwidth : 4 * η ≤ Real.sin b) :
    ∃ δ C W : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧ 0 < W ∧
      ∀ (n : ℕ) (ε : ℝ), 0 < ε → ε ≤ δ →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 → ∀ μ r : ℝ, 0 < r →
      ∀ σ : ℂ, σ = 1 ∨ σ = -1 →
        (∫ x in actualCenteredShell (n + 1) (μ - b) b δ r,
          actualSignedFullDensity (isotropicRadialParameter α ε) σ η τ ξ
            (centeredConstraintAngles (μ - b) x)) ≤
          (C * (n + 2) ^ 3 * Real.sqrt (|μ| + r + ε) / r * (1 + |Real.log ε|)) *
            (24 * W * r / Real.sqrt (|μ| + r + ε)) ^ n := by
  obtain ⟨δ, C, W, hδ, hδ1, hC, hW, hbound⟩ :=
    exists_actual_complete_shell_coarea α b η hα hb hpoint hη hwidth
  refine ⟨δ, C, W, hδ, hδ1, hC, hW, ?_⟩
  intro n ε hε hεδ τ ξ hτ hξ μ r hr σ hσ
  rcases hσ with rfl | rfl
  · simpa only [actualFullPhaseDensity_zero_eq_signed] using hbound n ε hε hεδ τ ξ hτ hξ μ r 0 hr
  · simpa only [actualFullPhaseDensity_pi_eq_signed] using hbound n ε hε hεδ τ ξ hτ hξ μ r Real.pi hr

theorem shell_scale_power_identity (n : ℕ) (C A N μ r ε L : ℝ)
    (hr : 0 < r) (hε : 0 < ε) :
    (C * N ^ 3 * Real.sqrt (|μ| + r + ε) / r * L) *
      (A * r / Real.sqrt (|μ| + r + ε)) ^ (n + 1) =
      (C * A ^ (n + 1)) * N ^ 3 * (r / Real.sqrt (|μ| + r + ε)) ^ n * L := by
  have hs : Real.sqrt (|μ| + r + ε) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  have hu : (Real.sqrt (|μ| + r + ε) / r) * (r / Real.sqrt (|μ| + r + ε)) = 1 := by
    field_simp
  calc
    _ = (C * A ^ (n + 1)) * N ^ 3 * (r / Real.sqrt (|μ| + r + ε)) ^ n * L *
        ((Real.sqrt (|μ| + r + ε) / r) * (r / Real.sqrt (|μ| + r + ε))) := by
      rw [show A * r / Real.sqrt (|μ| + r + ε) = A * (r / Real.sqrt (|μ| + r + ε)) by ring,
        mul_pow, pow_succ (r / Real.sqrt (|μ| + r + ε))]
      ring
    _ = _ := by rw [hu, mul_one]

/-- Frozen complete right-shell coarea: all physical factors, every
fixed mean and every N>=3, with constants chosen before N. -/
theorem exists_actual_signed_shell_delta_bound (α b η : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α)
    (hη : 0 < η) (hwidth : 4 * η ≤ Real.sin b) :
    ∃ δ K : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 1 ≤ K ∧
      ∀ (n : ℕ) (ε : ℝ), 0 < ε → ε ≤ δ →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 → ∀ μ r : ℝ, 0 < r →
      ∀ σ : ℂ, σ = 1 ∨ σ = -1 →
        (∫ x in actualCenteredShell (n + 2) (μ - b) b δ r,
          actualSignedFullDensity (isotropicRadialParameter α ε) σ η τ ξ
            (centeredConstraintAngles (μ - b) x)) ≤
          K ^ (n + 3) * (n + 3) ^ 3 *
            (r / Real.sqrt (|μ| + r + ε)) ^ n * (1 + |Real.log ε|) := by
  obtain ⟨δ, C, W, hδ, hδ1, hC, hW, hbound⟩ :=
    exists_actual_complete_signed_shell_coarea α b η hα hb hpoint hη hwidth
  let K := max 1 (max C (24 * W))
  have hK1 : 1 ≤ K := le_max_left _ _
  have hK : 0 < K := lt_of_lt_of_le (by norm_num) hK1
  have hCK : C ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hAK : 24 * W ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨δ, K, hδ, hδ1, hK1, ?_⟩
  intro n ε hε hεδ τ ξ hτ hξ μ r hr σ hσ
  have hmain := hbound (n + 1) ε hε hεδ τ ξ hτ hξ μ r hr σ hσ
  have heN : ((n + 1 : ℕ) : ℝ) + 2 = (n : ℝ) + 3 := by push_cast; ring
  simp only [heN] at hmain
  rw [shell_scale_power_identity n C (24 * W) _ μ r ε _ hr hε] at hmain
  have hp : C * (24 * W) ^ (n + 1) ≤ K ^ (n + 3) := by
    calc
      _ ≤ K * K ^ (n + 1) := mul_le_mul hCK (pow_le_pow_left₀ (by positivity) hAK _)
        (by positivity) hK.le
      _ = K ^ (n + 2) := by rw [pow_succ K (n + 1)]; ring
      _ ≤ K ^ (n + 3) := by
        rw [pow_succ K (n + 2)]
        exact le_mul_of_one_le_right (by positivity) hK1
  exact hmain.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp (by positivity)) (by positivity))
    (by positivity))

end IsingBulk.AnisoF002.Isotropic
