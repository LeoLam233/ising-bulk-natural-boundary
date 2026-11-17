import IsingBulk.AnisoF002.C03.IsotropicCutoffDescendantBuffer

/-!
# The actual angular flux velocity on the protected right shell

The complete inverse balanced Jacobian and actual inverse-coordinate
coefficients give a polynomial particle cost and one inverse shell
power. This bound is used only with the retained collision amplitude.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Metric Filter
open scoped Topology BigOperators

theorem exists_actual_velocity_shell_buffer (α b : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α) :
    ∃ β : ℝ, 0 < β ∧ β ≤ 1 ∧ ∀ η : ℝ, 0 < η → 4 * η ≤ Real.sin b →
      ∃ δ C : ℝ, 0 < δ ∧ δ ≤ β ∧ 0 < C ∧
      ∀ (N : ℕ), 0 < N → ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ θ : Fin N → ℝ, (∀ i, θ i ∈ Icc (-b - β) β) →
      ∀ r : ℝ, 0 < r → (∀ i l, |θ i - θ l| ≤ 2 * r) → (∃ i l, r ≤ |θ i - θ l|) →
      ∀ i : Fin N, ‖actualCovarianceAngularVelocity η τ ξ i (isotropicRadialParameter α ε, θ)‖ ≤
        C * (N : ℝ) ^ 3 / isotropicShellDelta b ε r θ := by
  obtain ⟨βA, hβA, hβA1, hballsAll⟩ := exists_actual_complete_cutoff_transport_buffer α b hα hb hpoint
  have hcoslo := Real.cos_lt_cos_of_nonneg_of_le_pi hb.1.le le_rfl hb.2
  have hcoshi := Real.cos_lt_cos_of_nonneg_of_le_pi (show (0 : ℝ) ≤ 0 by norm_num) hb.2.le hb.1
  rw [Real.cos_pi] at hcoslo
  rw [Real.cos_zero] at hcoshi
  have hS : 0 < 2 * Real.cos α ∧ 2 * Real.cos α < 2 := by
    constructor <;> linarith only [hpoint, hcoslo, hcoshi]
  have hbS : rightBranchEndpoint (2 * Real.cos α) = b := by
    unfold rightBranchEndpoint
    rw [show 2 * Real.cos α - 1 = Real.cos b by linarith only [hpoint]]
    exact Real.arccos_cos hb.1.le hb.2.le
  obtain ⟨βF, hβF, _, hframeAll⟩ := exists_actual_physical_frame_buffer (2 * Real.cos α) hS
  let β := min βA βF
  have hβ : 0 < β := lt_min hβA hβF
  have hβA' : β ≤ βA := min_le_left _ _
  have hβF' : β ≤ βF := min_le_right _ _
  have hβ1 : β ≤ 1 := hβA'.trans hβA1
  refine ⟨β, hβ, hβ1, ?_⟩
  intro η hη hwidth
  obtain ⟨δA, κ, C, M, c, B, K, hδA, _, _, _, _, hc, _, hK, hballs⟩ := hballsAll η hη hwidth
  obtain ⟨δF, hδF, _, hinv, hframe⟩ := hframeAll η hη
  obtain ⟨CA, hCA, hA⟩ := hinv 0
  let δ := min β (min δA (δF / 8))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδβ : δ ≤ β := min_le_left _ _
  have hδA' : δ ≤ δA := (min_le_right _ _).trans (min_le_left _ _)
  have hδ1 : δ ≤ 1 := hδβ.trans hβ1
  have hδF8 : δ ≤ δF / 8 := (min_le_right _ _).trans (min_le_right _ _)
  have hδF' : δ ≤ δF := by linarith only [hδF8, hδF]
  refine ⟨δ, CA * K, hδ, hδβ, mul_pos hCA hK, ?_⟩
  intro N hN ε hε hεδ τ ξ hτ hξ θ hθ r hr hdiam hdiamLower i
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  let s := isotropicRadialParameter α ε
  let q := actualHomotopyRegularTuple s η τ ξ θ
  let Δ := isotropicShellDelta b ε r θ
  have hΔ : 0 < Δ := isotropicShellDelta_pos b ε r θ hε hr
  obtain ⟨_, hball⟩ := hballs N hN ∅ (Finset.empty_subset _) ε hε (hεδ.trans hδA') τ ξ
    ⟨hτ.1, hτ.2.trans hδA'⟩ hξ θ
    (fun i => ⟨by linarith only [(hθ i).1, hβA'], (hθ i).2.trans hβA'⟩)
    r hr hdiam hdiamLower
  have hqball : q ∈ ball q (c * Δ / (N : ℝ) ^ 2) := mem_ball_self (by positivity)
  have hrad := isotropicRadialParameter_estimates α ε hα hε (hεδ.trans hδ1)
  have hsF : dist s ((2 * Real.cos α : ℝ) : ℂ) < δF :=
    hrad.2.2.2.2.trans_lt (by linarith only [hεδ, hδF8, hδF])
  have hθF : ∀ j, θ j ∈ Icc (-rightBranchEndpoint (2 * Real.cos α) - βF) βF := by
    intro j
    rw [hbS]
    exact ⟨by linarith only [(hθ j).1, hβF'], (hθ j).2.trans hβF'⟩
  obtain ⟨_, _, _, hV⟩ := hframe N hN s hrad.2.2.2.1 hsF τ ξ
    ⟨hτ.1, hτ.2.trans hδF'⟩ hξ θ hθF
  rw [hV.self_of_nhds i, norm_neg]
  calc
    _ ≤ ∑ j, ‖actualBalancedInverseEntry η τ ξ i j θ * rightCutoffTransportCoefficient q j‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _j : Fin N, CA * (K * (N : ℝ) ^ 2 / Δ) := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      have hj : ‖actualBalancedInverseEntry η τ ξ i j θ‖ ≤ CA := by
        have hh := (hA N hN τ ξ ⟨hτ.1, hτ.2.trans hδF'⟩ hξ i j).bound 0 le_rfl θ
        simpa only [norm_iteratedFDeriv_zero, mul_zero, pow_zero, mul_one] using hh
      exact mul_le_mul hj ((hball q hqball).2.2.2.2 j).2 (norm_nonneg _) hCA.le
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

end
end IsingBulk.AnisoF002.Isotropic
