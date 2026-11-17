import IsingBulk.AnisoF002.C03.IsotropicActualTransportBalls

/-!
# Actual all-order analytic numerator transport with retained collision degree

Every derivative in every previous descendant is retained. The physical
image and the common protected ball are constructed internally. This
is the analytic numerator part of the full real-frame recurrence; real
cutoffs and the integrated current are separate remaining steps.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

theorem exists_actual_complete_analytic_descendant_jets (α b η : ℝ)
    (hα : 0 < α ∧ α < Real.pi) (hb : 0 < b ∧ b < Real.pi)
    (hpoint : 1 + Real.cos b = 2 * Real.cos α)
    (hη : 0 < η) (hwidth : 4 * η ≤ Real.sin b) :
    ∃ δ κ C M : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < κ ∧ 0 < C ∧ 0 < M ∧
      ∀ j k : ℕ, ∃ Cjk : ℝ, 0 < Cjk ∧
      ∀ (N : ℕ), 0 < N → ∀ (R : Finset (Fin N × Fin N)), R ⊆ indexPairs N →
      ∀ ε : ℝ, 0 < ε → ε ≤ δ → ∀ τ ξ : ℝ, τ ∈ Icc 0 δ → ξ ∈ Icc 0 1 →
      ∀ θ : Fin N → ℝ, (∀ i, θ i ∈ Icc (-b - δ) δ) →
      ∀ r : ℝ, 0 < r → (∀ i l, |θ i - θ l| ≤ 2 * r) → (∃ i l, r ≤ |θ i - θ l|) →
        let q := actualHomotopyRegularTuple (isotropicRadialParameter α ε) η τ ξ θ
        let Δ := isotropicShellDelta b ε r θ
        ‖iteratedFDeriv ℂ k (analyticTransportDescendant
          (fun p : RegularJointSpace N => rightCovarianceField p.1 p.2)
          (completeRegularNumerator N) j) q‖ ≤
          Cjk * (N : ℝ) ^ (5 * j + 2 * k) * C ^ N * M ^ R.card *
            Real.exp (-κ * (N : ℝ) ^ 2 + (1 / 2 : ℝ) * N) *
              Δ ^ (2 * R.card) / Δ ^ (2 * j + k) := by
  obtain ⟨δ, κ, C, M, c, B, hδ, hδ1, hκ, hC, hM, hc, hB, hballs⟩ :=
    exists_actual_complete_transport_balls α b η hα hb hpoint hη hwidth
  let D₀ := Real.sqrt (Real.pi + 2)
  have hD₀ : 0 < D₀ := Real.sqrt_pos.mpr (by positivity)
  refine ⟨δ, κ, C, M, hδ, hδ1, hκ, hC, hM, ?_⟩
  intro j k
  refine ⟨scaledTransportJetConstant j k c B D₀,
    scaledTransportJetConstant_pos j k c B D₀ hc hB hD₀, ?_⟩
  intro N hN R hR ε hε hεδ τ ξ hτ hξ θ hθ r hr hdiam hdiamLower
  dsimp only
  let q := actualHomotopyRegularTuple (isotropicRadialParameter α ε) η τ ξ θ
  let Δ := isotropicShellDelta b ε r θ
  have hΔ : 0 < Δ := isotropicShellDelta_pos b ε r θ hε hr
  obtain ⟨hΔD, hball⟩ := hballs N hN R hR ε hε hεδ τ ξ hτ hξ θ hθ r hr hdiam hdiamLower
  have hh := analyticTransportDescendant_scaled_joint_jets hN
    (fun p : RegularJointSpace N => rightCovarianceField p.1 p.2) (completeRegularNumerator N)
    q c B D₀ Δ
    (C ^ N * M ^ R.card * Real.exp (-κ * (N : ℝ) ^ 2 + (1 / 2 : ℝ) * N))
    (2 * R.card) j k hc hB hD₀ hΔ hΔD (by positivity)
    (fun p hp => (hball p hp).1) (fun p hp => (hball p hp).2.2.1)
    (fun p hp => (hball p hp).2.1) (fun p hp => (hball p hp).2.2.2)
  exact hh.trans_eq (by ring)

end IsingBulk.AnisoF002.Isotropic
