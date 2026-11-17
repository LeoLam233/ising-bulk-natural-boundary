import IsingBulk.AnisoF002.C03.IsotropicScaledWordBounds
import IsingBulk.AnisoF002.C03.IsotropicActualWordExpansion

/-!
# The full finite word sum retains Gaussian collision suppression

The count (1+N²)^j includes every cutoff branch. At each fixed order it
costs a polynomial in N, as do all full inverse-Jacobian jets. No branch
or derivative of a preceding coefficient is discarded.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

theorem transportWord_card_real_le {N : ℕ} (hN : 0 < N) (n : ℕ) :
    (Fintype.card (TransportWord N n) : ℝ) ≤ 2 ^ n * (N : ℝ) ^ (2 * n) := by
  rw [transportWord_card, Nat.cast_pow, Nat.cast_add, Nat.cast_one, Nat.cast_pow]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := one_le_pow₀ hN1
  have hh : 1 + (N : ℝ) ^ 2 ≤ 2 * (N : ℝ) ^ 2 := by linarith only [hN2]
  exact (pow_le_pow_left₀ (by positivity) hh n).trans_eq (by rw [mul_pow, ← pow_mul])

def separatedWordBoundConstant (n k : ℕ) (c B K D₀ CA : ℝ) : ℝ :=
  2 ^ n * scaledWordConstant n c B K D₀ * (2 ^ k * CA) ^ n

theorem separatedWordBoundConstant_pos (n k : ℕ) (c B K D₀ CA : ℝ)
    (hc : 0 < c) (hB : 0 < B) (hK : 0 < K) (hD : 0 < D₀) (hCA : 0 < CA) :
    0 < separatedWordBoundConstant n k c B K D₀ CA := by
  unfold separatedWordBoundConstant
  have hh := scaledWordConstant_pos n c B K D₀ hc hB hK hD
  positivity

theorem separatedWordSum_scaled_bound {N : ℕ} (hN : 0 < N)
    (B K : RegularJointSpace N → Fin N → ℂ) (F : RegularJointSpace N → ℂ)
    (A : Fin N → Fin N → (Fin N → ℝ) → ℂ) (g : (Fin N → ℝ) → ℂ)
    (q : RegularJointSpace N) (θ : Fin N → ℝ) (c B₀ K₀ D₀ Δ E₀ CA Cg : ℝ)
    (d n k : ℕ) (hnk : n ≤ k)
    (hc : 0 < c) (hB₀ : 0 < B₀) (hK₀ : 0 < K₀) (hD₀ : 0 < D₀)
    (hΔ : 0 < Δ) (hΔD : Δ ≤ D₀) (hE : 0 ≤ E₀) (hCA : 1 ≤ CA) (hCg : 0 ≤ Cg)
    (hB : AnalyticOnNhd ℂ B (ball q (c * Δ / (N : ℝ) ^ 2)))
    (hK : ∀ j, AnalyticOnNhd ℂ (fun p => K p j) (ball q (c * Δ / (N : ℝ) ^ 2)))
    (hF : AnalyticOnNhd ℂ F (ball q (c * Δ / (N : ℝ) ^ 2)))
    (hBL : ∀ p ∈ ball q (c * Δ / (N : ℝ) ^ 2), ‖B p‖ ≤ B₀ * (N : ℝ) ^ 2 / Δ)
    (hKL : ∀ p ∈ ball q (c * Δ / (N : ℝ) ^ 2), ∀ j, ‖K p j‖ ≤ K₀ * (N : ℝ) ^ 2 / Δ)
    (hFL : ∀ p ∈ ball q (c * Δ / (N : ℝ) ^ 2), ‖F p‖ ≤ E₀ * Δ ^ d)
    (hA : ∀ i j, FiniteJetControl k (A i j) (CA * (N : ℝ) ^ (3 * k)))
    (hg : FiniteJetControl k g Cg) :
    ‖∑ w : TransportWord N n,
      transportAnalyticWord B K F n w q * transportAngularWord A g n w θ‖ ≤
      separatedWordBoundConstant n k c B₀ K₀ D₀ CA * (N : ℝ) ^ ((7 + 3 * k) * n) *
        E₀ * Cg * Δ ^ d / Δ ^ (2 * n) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hCA' : 1 ≤ CA * (N : ℝ) ^ (3 * k) :=
    one_le_mul_of_one_le_of_one_le hCA (one_le_pow₀ hN1)
  let LA := scaledWordConstant n c B₀ K₀ D₀ * (N : ℝ) ^ (5 * n) * E₀ * Δ ^ d / Δ ^ (2 * n)
  let LG := (2 ^ k * (CA * (N : ℝ) ^ (3 * k))) ^ n * Cg
  have hLA : 0 ≤ LA := by
    dsimp [LA]
    have hh := (scaledWordConstant_pos n c B₀ K₀ D₀ hc hB₀ hK₀ hD₀).le
    positivity
  have hLG : 0 ≤ LG := by dsimp [LG]; positivity
  have hf (w : TransportWord N n) : ‖transportAnalyticWord B K F n w q‖ ≤ LA :=
    transportAnalyticWord_scaled_bound hN B K F q c B₀ K₀ D₀ Δ E₀ d n
      hc hB₀ hK₀ hD₀ hΔ hΔD hE hB hK hF hBL hKL hFL w q (mem_ball_self (by positivity))
  have hg' (w : TransportWord N n) : ‖transportAngularWord A g n w θ‖ ≤ LG := by
    have hh := (transportAngularWord_finite_jet_bound A g (CA * (N : ℝ) ^ (3 * k)) Cg
      hCA' hCg hA hg n hnk w).bound 0 (Nat.zero_le _) θ
    simpa only [norm_iteratedFDeriv_zero] using hh
  calc
    _ ≤ ∑ w : TransportWord N n, ‖transportAnalyticWord B K F n w q * transportAngularWord A g n w θ‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _w : TransportWord N n, LA * LG := by
      apply Finset.sum_le_sum
      intro w _
      rw [norm_mul]
      exact mul_le_mul (hf w) (hg' w) (norm_nonneg _) hLA
    _ = (Fintype.card (TransportWord N n) : ℝ) * (LA * LG) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (2 ^ n * (N : ℝ) ^ (2 * n)) * (LA * LG) :=
      mul_le_mul_of_nonneg_right (transportWord_card_real_le hN n) (mul_nonneg hLA hLG)
    _ = _ := by
      have hNpow : (N : ℝ) ^ (2 * n) * (N : ℝ) ^ (5 * n) * (N : ℝ) ^ ((3 * k) * n) =
          (N : ℝ) ^ ((7 + 3 * k) * n) := by
        rw [← pow_add, ← pow_add]
        congr 1
        ring
      have hGpow : (2 ^ k * (CA * (N : ℝ) ^ (3 * k))) ^ n =
          (2 ^ k * CA) ^ n * (N : ℝ) ^ ((3 * k) * n) := by
        rw [← mul_assoc, mul_pow, ← pow_mul]
      dsimp only [LA, LG, separatedWordBoundConstant]
      rw [hGpow]
      calc
        _ = (2 ^ n * scaledWordConstant n c B₀ K₀ D₀ * (2 ^ k * CA) ^ n) *
            ((N : ℝ) ^ (2 * n) * (N : ℝ) ^ (5 * n) * (N : ℝ) ^ ((3 * k) * n)) *
            E₀ * Cg * Δ ^ d / Δ ^ (2 * n) := by ring
        _ = _ := by rw [hNpow]

end IsingBulk.AnisoF002.Isotropic
