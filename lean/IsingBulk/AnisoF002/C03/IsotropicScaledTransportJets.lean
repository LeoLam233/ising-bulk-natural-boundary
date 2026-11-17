import IsingBulk.AnisoF002.C03.IsotropicAnalyticTransportIteration

/-!
# Retained-degree estimates for every complete analytic descendant

At the actual protected scale c Δ/N² the complete covariance field is
O(N²/Δ). Every application of the full transport operator costs only
a fixed polynomial in N and two powers of Δ. Every further joint jet
is included, without holding any coefficient or parameter fixed.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Metric

def scaledTransportJetConstant (j k : ℕ) (c B D₀ : ℝ) : ℝ :=
  protectedJetConstant k (c / 2 ^ j) * transportBallConstant j *
    (D₀ + 2 * B) ^ j / c ^ j

theorem scaledTransportJetConstant_pos (j k : ℕ) (c B D₀ : ℝ)
    (hc : 0 < c) (hB : 0 < B) (hD : 0 < D₀) :
    0 < scaledTransportJetConstant j k c B D₀ := by
  have hk := protectedJetConstant_pos k (by positivity : 0 < c / 2 ^ j)
  have hj := transportBallConstant_pos j
  unfold scaledTransportJetConstant
  positivity

theorem covariance_transport_scale_bound (N : ℕ) (hN : 0 < N)
    (B D₀ Δ : ℝ) (hD : 0 ≤ D₀) (hΔ : 0 < Δ) (hΔD : Δ ≤ D₀) :
    1 + 2 * (N : ℝ) * (B * (N : ℝ) ^ 2 / Δ) ≤
      (D₀ + 2 * B) * (N : ℝ) ^ 3 / Δ := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hpow : (1 : ℝ) ≤ (N : ℝ) ^ 3 := one_le_pow₀ hN1
  have hle : Δ ≤ D₀ * (N : ℝ) ^ 3 := hΔD.trans (le_mul_of_one_le_right hD hpow)
  apply (le_div_iff₀ hΔ).mpr
  have he : (1 + 2 * (N : ℝ) * (B * (N : ℝ) ^ 2 / Δ)) * Δ =
      Δ + 2 * B * (N : ℝ) ^ 3 := by field_simp
  rw [he]
  nlinarith only [hle]

/-- Complete iterates and complete joint jets preserve D−2j−k powers
of the shell coordinate scale, in denominator form valid at all orders. -/
theorem analyticTransportDescendant_scaled_joint_jets {N : ℕ} (hN : 0 < N)
    (Bfield : RegularJointSpace N → Fin N → ℂ) (b : RegularJointSpace N → ℂ)
    (q : RegularJointSpace N) (c B D₀ Δ E₀ : ℝ) (d j k : ℕ)
    (hc : 0 < c) (hB : 0 < B) (hD : 0 < D₀) (hΔ : 0 < Δ) (hΔD : Δ ≤ D₀)
    (hE : 0 ≤ E₀)
    (hBa : AnalyticOnNhd ℂ Bfield (ball q (c * Δ / (N : ℝ) ^ 2)))
    (hba : AnalyticOnNhd ℂ b (ball q (c * Δ / (N : ℝ) ^ 2)))
    (hBL : ∀ p ∈ ball q (c * Δ / (N : ℝ) ^ 2), ‖Bfield p‖ ≤ B * (N : ℝ) ^ 2 / Δ)
    (hbM : ∀ p ∈ ball q (c * Δ / (N : ℝ) ^ 2), ‖b p‖ ≤ E₀ * Δ ^ d) :
    ‖iteratedFDeriv ℂ k (analyticTransportDescendant Bfield b j) q‖ ≤
      scaledTransportJetConstant j k c B D₀ * (N : ℝ) ^ (5 * j + 2 * k) *
        E₀ * Δ ^ d / Δ ^ (2 * j + k) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hrad : 0 < c * Δ / (N : ℝ) ^ 2 := by positivity
  have hh := analyticTransportDescendant_joint_jet_bound Bfield b q
    (c * Δ / (N : ℝ) ^ 2) (B * (N : ℝ) ^ 2 / Δ) (E₀ * Δ ^ d)
    hrad (by positivity) hBa hba hBL hbM j k
  have hscale := covariance_transport_scale_bound N hN B D₀ Δ hD.le hΔ hΔD
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + 2 * (N : ℝ) *
    (B * (N : ℝ) ^ 2 / Δ)) hscale j
  have hconst : 0 ≤ protectedJetConstant k ((c * Δ / (N : ℝ) ^ 2) / 2 ^ j) :=
    (protectedJetConstant_pos k (by positivity)).le
  have hK : 0 ≤ transportBallConstant j := (transportBallConstant_pos j).le
  have hEΔ : 0 ≤ E₀ * Δ ^ d := mul_nonneg hE (pow_nonneg hΔ.le d)
  calc
    _ ≤ protectedJetConstant k ((c * Δ / (N : ℝ) ^ 2) / 2 ^ j) *
        (transportBallConstant j * (1 + 2 * (N : ℝ) * (B * (N : ℝ) ^ 2 / Δ)) ^ j /
          (c * Δ / (N : ℝ) ^ 2) ^ j * (E₀ * Δ ^ d)) := hh
    _ ≤ protectedJetConstant k ((c * Δ / (N : ℝ) ^ 2) / 2 ^ j) *
        (transportBallConstant j * ((D₀ + 2 * B) * (N : ℝ) ^ 3 / Δ) ^ j /
          (c * Δ / (N : ℝ) ^ 2) ^ j * (E₀ * Δ ^ d)) := by
      apply mul_le_mul_of_nonneg_left _ hconst
      apply mul_le_mul_of_nonneg_right _ hEΔ
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hK) (by positivity)
    _ = _ := by
      rw [show (c * Δ / (N : ℝ) ^ 2) / 2 ^ j =
        ((c / 2 ^ j) * Δ) / (N : ℝ) ^ 2 by ring]
      rw [protectedJetConstant_div k _ _ (pow_ne_zero 2 hNr.ne'),
        protectedJetConstant_mul_scale k _ Δ hΔ.ne']
      simp only [scaledTransportJetConstant, mul_pow, div_pow, ← pow_mul, pow_add]
      field_simp
      ring

end IsingBulk.AnisoF002.Isotropic
