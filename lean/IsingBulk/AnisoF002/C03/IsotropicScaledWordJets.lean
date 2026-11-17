import IsingBulk.AnisoF002.C03.IsotropicScaledWordBounds

/-!
# Complete joint jets of the separated analytic cutoff words

Every additional joint derivative is taken on the complete analytic word.
The retained collision degree loses exactly one further power of Δ per jet.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Metric
open scoped Topology BigOperators

def scaledWordJetConstant (n k : ℕ) (c B K D₀ : ℝ) : ℝ :=
  protectedJetConstant k (c / 2 ^ n) * scaledWordConstant n c B K D₀

theorem scaledWordJetConstant_pos (n k : ℕ) (c B K D₀ : ℝ)
    (hc : 0 < c) (hB : 0 < B) (hK : 0 < K) (hD : 0 < D₀) :
    0 < scaledWordJetConstant n k c B K D₀ :=
  mul_pos (protectedJetConstant_pos k (by positivity))
    (scaledWordConstant_pos n c B K D₀ hc hB hK hD)

theorem transportAnalyticWord_scaled_joint_jets {N : ℕ} (hN : 0 < N)
    (B K : RegularJointSpace N → Fin N → ℂ) (F : RegularJointSpace N → ℂ)
    (q : RegularJointSpace N) (c B₀ K₀ D₀ Δ E₀ : ℝ) (d n k : ℕ)
    (hc : 0 < c) (hB₀ : 0 < B₀) (hK₀ : 0 < K₀) (hD₀ : 0 < D₀)
    (hΔ : 0 < Δ) (hΔD : Δ ≤ D₀) (hE : 0 ≤ E₀)
    (hB : AnalyticOnNhd ℂ B (ball q (c * Δ / (N : ℝ) ^ 2)))
    (hK : ∀ j, AnalyticOnNhd ℂ (fun p => K p j) (ball q (c * Δ / (N : ℝ) ^ 2)))
    (hF : AnalyticOnNhd ℂ F (ball q (c * Δ / (N : ℝ) ^ 2)))
    (hBL : ∀ p ∈ ball q (c * Δ / (N : ℝ) ^ 2), ‖B p‖ ≤ B₀ * (N : ℝ) ^ 2 / Δ)
    (hKL : ∀ p ∈ ball q (c * Δ / (N : ℝ) ^ 2), ∀ j, ‖K p j‖ ≤ K₀ * (N : ℝ) ^ 2 / Δ)
    (hFL : ∀ p ∈ ball q (c * Δ / (N : ℝ) ^ 2), ‖F p‖ ≤ E₀ * Δ ^ d)
    (w : TransportWord N n) :
    ‖iteratedFDeriv ℂ k (transportAnalyticWord B K F n w) q‖ ≤
      scaledWordJetConstant n k c B₀ K₀ D₀ * (N : ℝ) ^ (5 * n + 2 * k) *
        E₀ * Δ ^ d / Δ ^ (2 * n + k) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hrad : 0 < c * Δ / (N : ℝ) ^ 2 := by positivity
  have hsub : ball q ((c * Δ / (N : ℝ) ^ 2) / 2 ^ n) ⊆
      ball q (c * Δ / (N : ℝ) ^ 2) :=
    ball_subset_ball (div_le_self hrad.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)))
  have hh := analytic_ball_joint_jet_bound k (transportAnalyticWord B K F n w) q
    ((c * Δ / (N : ℝ) ^ 2) / 2 ^ n)
    (scaledWordConstant n c B₀ K₀ D₀ * (N : ℝ) ^ (5 * n) * E₀ * Δ ^ d / Δ ^ (2 * n))
    (by positivity)
    (fun p hp => transportAnalyticWord_analyticAt B K F p (hB p (hsub hp))
      (fun j => hK j p (hsub hp)) (hF p (hsub hp)) n w)
    (fun p hp => transportAnalyticWord_scaled_bound hN B K F q c B₀ K₀ D₀ Δ E₀ d n
      hc hB₀ hK₀ hD₀ hΔ hΔD hE hB hK hF hBL hKL hFL w p hp)
  exact hh.trans_eq (by
    rw [show (c * Δ / (N : ℝ) ^ 2) / 2 ^ n =
      ((c / 2 ^ n) * Δ) / (N : ℝ) ^ 2 by ring]
    rw [protectedJetConstant_div k _ _ (pow_ne_zero 2 hNr.ne'),
      protectedJetConstant_mul_scale k _ Δ hΔ.ne']
    simp only [scaledWordJetConstant, ← pow_mul, pow_add]
    field_simp)

end
end IsingBulk.AnisoF002.Isotropic
