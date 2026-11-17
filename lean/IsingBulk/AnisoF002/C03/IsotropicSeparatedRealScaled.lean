import IsingBulk.AnisoF002.C03.IsotropicSeparatedRealJets

/-!
# The remaining collision degree in the complete first real jet

At fixed particle number and positive interior radial parameter the
regular coordinate map has a bounded first derivative.  The estimate
below isolates that bound and preserves D−2j−1 powers of the actual
shell scale, including every real-cutoff derivative.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set Metric
open scoped Topology BigOperators

theorem separatedWordSum_first_real_jet_scaled
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {N : ℕ} (hN : 0 < N)
    (B K : RegularJointSpace N → Fin N → ℂ) (F : RegularJointSpace N → ℂ)
    (A : Fin N → Fin N → (Fin N → ℝ) → ℂ) (g : (Fin N → ℝ) → ℂ)
    (q : E → RegularJointSpace N) (θ : E → (Fin N → ℝ)) (x : E)
    (c B₀ K₀ D₀ Δ E₀ CA Cg Q : ℝ) (d n k : ℕ) (hnk : n + 1 ≤ k)
    (hc : 0 < c) (hB₀ : 0 < B₀) (hK₀ : 0 < K₀) (hD₀ : 0 < D₀)
    (hΔ : 0 < Δ) (hΔD : Δ ≤ D₀) (hE : 0 ≤ E₀) (hCA : 1 ≤ CA)
    (hCg : 0 ≤ Cg) (hQ : 0 ≤ Q)
    (hB : AnalyticOnNhd ℂ B (ball (q x) (c * Δ / (N : ℝ) ^ 2)))
    (hK : ∀ j, AnalyticOnNhd ℂ (fun p => K p j) (ball (q x) (c * Δ / (N : ℝ) ^ 2)))
    (hF : AnalyticOnNhd ℂ F (ball (q x) (c * Δ / (N : ℝ) ^ 2)))
    (hBL : ∀ p ∈ ball (q x) (c * Δ / (N : ℝ) ^ 2), ‖B p‖ ≤ B₀ * (N : ℝ) ^ 2 / Δ)
    (hKL : ∀ p ∈ ball (q x) (c * Δ / (N : ℝ) ^ 2), ∀ j, ‖K p j‖ ≤ K₀ * (N : ℝ) ^ 2 / Δ)
    (hFL : ∀ p ∈ ball (q x) (c * Δ / (N : ℝ) ^ 2), ‖F p‖ ≤ E₀ * Δ ^ d)
    (hA : ∀ i j, FiniteJetControl k (A i j) CA) (hg : FiniteJetControl k g Cg)
    (hq : DifferentiableAt ℝ q x) (hθ : DifferentiableAt ℝ θ x)
    (hqQ : ‖fderiv ℝ q x‖ ≤ Q) (hθ₁ : ‖fderiv ℝ θ x‖ ≤ 1) :
    ‖fderiv ℝ (fun y => ∑ w : TransportWord N n,
      transportAnalyticWord B K F n w (q y) * transportAngularWord A g n w (θ y)) x‖ ≤
      (Fintype.card (TransportWord N n) : ℝ) * ((2 ^ k * CA) ^ n * Cg) *
        (scaledWordConstant n c B₀ K₀ D₀ * (N : ℝ) ^ (5 * n) * D₀ +
          scaledWordJetConstant n 1 c B₀ K₀ D₀ * (N : ℝ) ^ (5 * n + 2) * Q) *
            E₀ * Δ ^ d / Δ ^ (2 * n + 1) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  let R := E₀ * Δ ^ d / Δ ^ (2 * n + 1)
  let C₀ := scaledWordConstant n c B₀ K₀ D₀ * (N : ℝ) ^ (5 * n)
  let C₁ := scaledWordJetConstant n 1 c B₀ K₀ D₀ * (N : ℝ) ^ (5 * n + 2)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hC₀ : 0 ≤ C₀ := mul_nonneg
    (scaledWordConstant_pos n c B₀ K₀ D₀ hc hB₀ hK₀ hD₀).le (by positivity)
  have hC₁ : 0 ≤ C₁ := mul_nonneg
    (scaledWordJetConstant_pos n 1 c B₀ K₀ D₀ hc hB₀ hK₀ hD₀).le (by positivity)
  have hcenter : q x ∈ ball (q x) (c * Δ / (N : ℝ) ^ 2) := mem_ball_self (by positivity)
  have hf₀ (w : TransportWord N n) :
      ‖transportAnalyticWord B K F n w (q x)‖ ≤ (C₀ * D₀) * R := by
    have hh := transportAnalyticWord_scaled_bound hN B K F (q x) c B₀ K₀ D₀ Δ E₀ d n
      hc hB₀ hK₀ hD₀ hΔ hΔD hE hB hK hF hBL hKL hFL w (q x) (mem_ball_self (by positivity))
    calc
      _ ≤ C₀ * Δ * R := hh.trans_eq (by dsimp [C₀, R]; rw [pow_succ]; field_simp)
      _ ≤ (C₀ * D₀) * R := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hΔD hC₀) hR
  have hf₁ (w : TransportWord N n) :
      ‖fderiv ℂ (transportAnalyticWord B K F n w) (q x)‖ ≤ C₁ * R := by
    have hh := transportAnalyticWord_scaled_joint_jets hN B K F (q x) c B₀ K₀ D₀ Δ E₀ d n 1
      hc hB₀ hK₀ hD₀ hΔ hΔD hE hB hK hF hBL hKL hFL w
    simpa only [norm_iteratedFDeriv_one, mul_one, C₁, R, mul_assoc, mul_div_assoc] using hh
  have hh := separatedWordSum_first_real_jet_bound B K F A g q θ x n k hnk
    hCA hCg (mul_nonneg (mul_nonneg hC₀ hD₀.le) hR) (mul_nonneg hC₁ hR) hQ hA hg
    (hB _ hcenter) (fun j => hK j _ hcenter) (hF _ hcenter) hf₀ hf₁ hq hθ hqQ hθ₁
  exact hh.trans_eq (by dsimp [C₀, C₁, R]; ring)

end
end IsingBulk.AnisoF002.Isotropic
