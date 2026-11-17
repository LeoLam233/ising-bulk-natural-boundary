import IsingBulk.AnisoF002.C03.NegativeDensityLogIdentity
import IsingBulk.AnisoF002.C03.NegativeEvenPhaseBounds

/-!
# Complete finite-particle logarithmic costs

The estimates sum every particle and every unordered pair.  The common
scalar bounds are kept separate from these exact finite-sum operations.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open IsingBulk.AnisoF002.Isotropic Set Filter
open scoped Topology BigOperators

theorem sum_norm_le_sqrt_displacement (n : ℕ) (v : Fin n → ℂ) :
    (∑ i, ‖v i‖) ≤ Real.sqrt ((n : ℝ) * displacementSquare n v) := by
  have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : Fin n => (1 : ℝ)) (fun i => ‖v i‖)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one] at hs
  have hQ : 0 ≤ (n : ℝ) * displacementSquare n v :=
    mul_nonneg (Nat.cast_nonneg n) (displacementSquare_nonneg n v)
  have hsq := Real.sq_sqrt hQ
  have hr := Real.sqrt_nonneg ((n : ℝ) * displacementSquare n v)
  have hn : 0 ≤ ∑ i, ‖v i‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  change (∑ i, ‖v i‖) ^ 2 ≤ (n : ℝ) * displacementSquare n v at hs
  nlinarith

theorem sum_indexPairs_add_le {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (∑ ij ∈ indexPairs n, (a ij.1 + a ij.2)) ≤ 2 * (n : ℝ) * ∑ i, a i := by
  calc
    _ ≤ ∑ ij : Fin n × Fin n, (a ij.1 + a ij.2) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun ij _ _ => add_nonneg (ha ij.1) (ha ij.2))
    _ = _ := by
      simp only [Fintype.sum_prod_type, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
      ring

theorem completeNumeratorLog_norm_le {n : ℕ} {lb : ℂ} {h : Fin n → ℂ}
    {p : Fin n × Fin n → ℂ} {u : ℂ} {v : Fin n → ℂ}
    {δ : Fin n → ℝ} {K L : ℝ}
    (hK : 0 ≤ K) (hδ : ∀ i, 0 ≤ δ i)
    (hb : ‖lb‖ ≤ L * ‖u‖)
    (hone : ∀ i, ‖h i‖ ≤ K * δ i)
    (hpair : ∀ ij ∈ indexPairs n,
      ‖p ij‖ ≤ K * ((‖v ij.1‖ ^ 2 + δ ij.1) + (‖v ij.2‖ ^ 2 + δ ij.2))) :
    ‖completeNumeratorLog n lb h p‖ ≤
      (n : ℝ) ^ 2 * L * ‖u‖ + K * (∑ i, δ i) +
        4 * K * (n : ℝ) * (displacementSquare n v + ∑ i, δ i) := by
  have ho : ‖∑ i, h i‖ ≤ K * ∑ i, δ i := by
    apply (norm_sum_le _ _).trans
    simpa only [← Finset.mul_sum] using
      (Finset.sum_le_sum (s := Finset.univ) (fun i _ => hone i))
  have hp : (∑ ij ∈ indexPairs n, ‖p ij‖) ≤
      2 * K * (n : ℝ) * (displacementSquare n v + ∑ i, δ i) := by
    have hs := sum_indexPairs_add_le (fun i => ‖v i‖ ^ 2 + δ i)
      (fun i => add_nonneg (sq_nonneg _) (hδ i))
    have hh := Finset.sum_le_sum (fun ij hij => hpair ij hij)
    rw [← Finset.mul_sum] at hh
    calc
      _ ≤ K * ∑ ij ∈ indexPairs n, ((‖v ij.1‖ ^ 2 + δ ij.1) + (‖v ij.2‖ ^ 2 + δ ij.2)) := hh
      _ ≤ K * (2 * (n : ℝ) * ∑ i, (‖v i‖ ^ 2 + δ i)) := mul_le_mul_of_nonneg_left hs hK
      _ = _ := by rw [Finset.sum_add_distrib]; unfold displacementSquare; ring
  have hp' : ‖∑ ij ∈ indexPairs n, 2 * p ij‖ ≤
      4 * K * (n : ℝ) * (displacementSquare n v + ∑ i, δ i) := by
    rw [← Finset.mul_sum, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
    exact (mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans hp)
      (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)
  have hb' : ‖((n ^ 2 : ℕ) : ℂ) * lb‖ ≤ (n : ℝ) ^ 2 * L * ‖u‖ := by
    rw [norm_mul, norm_natCast, Nat.cast_pow]
    exact (mul_le_mul_of_nonneg_left hb (sq_nonneg _)).trans_eq (by ring)
  unfold completeNumeratorLog
  calc
    _ ≤ ‖((n ^ 2 : ℕ) : ℂ) * lb‖ + ‖∑ i, h i‖ + ‖∑ ij ∈ indexPairs n, 2 * p ij‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ _ := by linarith

theorem sum_even_phase_variation {n : ℕ} {g : ℂ × ℂ → ℂ}
    {τ d t γ : ℂ} {v : Fin n → ℂ} {K : ℝ}
    (hcenter : g (τ, d) = γ) (hK : 0 ≤ K)
    (hv : ∀ i, ‖g (t, d + v i) - g (τ, d)‖ ≤
      K * (‖t - τ‖ + ‖d‖ * ‖v i‖ + ‖v i‖ ^ 2)) :
    (∑ i, ‖g (t, d + v i) - γ‖) ≤
      K * ((n : ℝ) * ‖t - τ‖ +
        ‖d‖ * Real.sqrt ((n : ℝ) * displacementSquare n v) + displacementSquare n v) := by
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hv i)
  simp only [hcenter, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  have hs := sum_norm_le_sqrt_displacement n v
  have hm := mul_le_mul_of_nonneg_left hs (mul_nonneg hK (norm_nonneg d))
  unfold displacementSquare at *
  nlinarith

end
end IsingBulk.AnisoF002.NegativeHT
