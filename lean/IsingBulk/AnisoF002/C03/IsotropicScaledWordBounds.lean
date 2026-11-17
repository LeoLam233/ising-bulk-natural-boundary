import IsingBulk.AnisoF002.C03.IsotropicTransportWordBounds

/-!
# Retained collision degree for every analytic cutoff word

At the actual protected radius c Δ/N², covariance transport and
multiplication by the inverse-coordinate cutoff coefficient each cost
at most a fixed polynomial in N and two powers of Δ. All joint jets
are then taken on the whole word.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

def scaledWordConstant (n : ℕ) (c B K D₀ : ℝ) : ℝ :=
  transportBallConstant n * ((D₀ + 2 * B) / c + K * D₀) ^ n

theorem scaledWordConstant_pos (n : ℕ) (c B K D₀ : ℝ)
    (hc : 0 < c) (hB : 0 < B) (hK : 0 < K) (hD : 0 < D₀) :
    0 < scaledWordConstant n c B K D₀ := by
  unfold scaledWordConstant
  exact mul_pos (transportBallConstant_pos n) (pow_pos (by positivity) n)

theorem cutoff_word_scale_bound {N : ℕ} (hN : 0 < N) (c B K D₀ Δ : ℝ)
    (hc : 0 < c) (hK : 0 ≤ K) (hD : 0 ≤ D₀)
    (hΔ : 0 < Δ) (hΔD : Δ ≤ D₀) :
    (1 + 2 * (N : ℝ) * (B * (N : ℝ) ^ 2 / Δ)) / (c * Δ / (N : ℝ) ^ 2) +
      K * (N : ℝ) ^ 2 / Δ ≤
        ((D₀ + 2 * B) / c + K * D₀) * (N : ℝ) ^ 5 / Δ ^ 2 := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hscale := covariance_transport_scale_bound N hN B D₀ Δ hD hΔ hΔD
  have hfirst : (1 + 2 * (N : ℝ) * (B * (N : ℝ) ^ 2 / Δ)) / (c * Δ / (N : ℝ) ^ 2) ≤
      ((D₀ + 2 * B) / c) * (N : ℝ) ^ 5 / Δ ^ 2 := by
    exact (div_le_div_of_nonneg_right hscale (by positivity)).trans_eq (by field_simp)
  have hsecond : K * (N : ℝ) ^ 2 / Δ ≤ K * D₀ * (N : ℝ) ^ 5 / Δ ^ 2 := by
    have hpow : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ 5 := pow_le_pow_right₀ hN1 (by norm_num)
    have hh : K * (N : ℝ) ^ 2 * Δ ≤ K * D₀ * (N : ℝ) ^ 5 := by
      calc
        _ ≤ K * (N : ℝ) ^ 2 * D₀ := mul_le_mul_of_nonneg_left hΔD (by positivity)
        _ ≤ K * (N : ℝ) ^ 5 * D₀ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hK) hD
        _ = _ := by ring
    apply (le_div_iff₀ (pow_pos hΔ 2)).mpr
    convert hh using 1
    field_simp
  exact (add_le_add hfirst hsecond).trans_eq (by ring)

theorem transportAnalyticWord_scaled_bound {N : ℕ} (hN : 0 < N)
    (B K : RegularJointSpace N → Fin N → ℂ) (F : RegularJointSpace N → ℂ)
    (q : RegularJointSpace N) (c B₀ K₀ D₀ Δ E₀ : ℝ) (d n : ℕ)
    (hc : 0 < c) (hB₀ : 0 < B₀) (hK₀ : 0 < K₀) (hD₀ : 0 < D₀)
    (hΔ : 0 < Δ) (hΔD : Δ ≤ D₀) (hE : 0 ≤ E₀)
    (hB : AnalyticOnNhd ℂ B (ball q (c * Δ / (N : ℝ) ^ 2)))
    (hK : ∀ j, AnalyticOnNhd ℂ (fun p => K p j) (ball q (c * Δ / (N : ℝ) ^ 2)))
    (hF : AnalyticOnNhd ℂ F (ball q (c * Δ / (N : ℝ) ^ 2)))
    (hBL : ∀ p ∈ ball q (c * Δ / (N : ℝ) ^ 2), ‖B p‖ ≤ B₀ * (N : ℝ) ^ 2 / Δ)
    (hKL : ∀ p ∈ ball q (c * Δ / (N : ℝ) ^ 2), ∀ j, ‖K p j‖ ≤ K₀ * (N : ℝ) ^ 2 / Δ)
    (hFL : ∀ p ∈ ball q (c * Δ / (N : ℝ) ^ 2), ‖F p‖ ≤ E₀ * Δ ^ d)
    (w : TransportWord N n) (p : RegularJointSpace N)
    (hp : p ∈ ball q ((c * Δ / (N : ℝ) ^ 2) / 2 ^ n)) :
    ‖transportAnalyticWord B K F n w p‖ ≤
      scaledWordConstant n c B₀ K₀ D₀ * (N : ℝ) ^ (5 * n) * E₀ * Δ ^ d / Δ ^ (2 * n) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hh := transportAnalyticWord_ball_bound B K F q (c * Δ / (N : ℝ) ^ 2)
    (B₀ * (N : ℝ) ^ 2 / Δ) (K₀ * (N : ℝ) ^ 2 / Δ) (E₀ * Δ ^ d)
    (by positivity) (by positivity) (by positivity) (by positivity) hB hK hF hBL hKL hFL n w p hp
  have hscale := cutoff_word_scale_bound hN c B₀ K₀ D₀ Δ hc hK₀.le hD₀.le hΔ hΔD
  have hpow := pow_le_pow_left₀ (by positivity) hscale n
  have hcost := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpow (transportBallConstant_pos n).le) (show 0 ≤ E₀ * Δ ^ d by positivity)
  exact hh.trans (hcost.trans_eq (by
    simp only [scaledWordConstant, mul_pow, div_pow, ← pow_mul]
    ring))

end IsingBulk.AnisoF002.Isotropic
