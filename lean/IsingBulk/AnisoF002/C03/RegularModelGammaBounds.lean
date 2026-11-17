import IsingBulk.AnisoF002.C03.RegularModelExactLog

/-!
# Paired finite gamma-factor estimates on the actual odd lattice

The exact correction E_j(alpha_n) is controlled by pairing exponent
blocks before estimating.  The estimates retain the first-difference
O(d*x^3/j) and second-difference O(d^2*x^2/j) scales.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open scoped BigOperators

theorem model_gamma_block_bounds (J : ℝ) (a b : ℕ) (hJ : 0 < J) (hab : a ≤ b)
    (hrange : 2 * (b : ℝ) ≤ J) :
    0 ≤ logGammaCorrection J b - logGammaCorrection J a ∧
      logGammaCorrection J b - logGammaCorrection J a ≤ 2 * ((b : ℝ) - a) * b / J := by
  have he : b = a + (b - a) := (Nat.add_sub_of_le hab).symm
  have hb := logGammaCorrection_block J a (b - a)
  rw [← he] at hb
  rw [hb]
  have ht (i : ℕ) (hi : i ∈ Finset.range (b - a)) :
      0 ≤ -Real.log (1 - ((a + i : ℕ) : ℝ) / J) ∧
        -Real.log (1 - ((a + i : ℕ) : ℝ) / J) ≤ 2 * (b : ℝ) / J := by
    have hib : a + i ≤ b := by have hi' := Finset.mem_range.mp hi; omega
    have hibR : ((a + i : ℕ) : ℝ) ≤ b := by exact_mod_cast hib
    have h := gamma_factor_increment_bounds J 0 ((a + i : ℕ) : ℝ) hJ (by positivity) (by linarith)
    simp only [zero_div, sub_zero, Real.log_one, neg_zero] at h
    exact ⟨h.1, h.2.trans (div_le_div_of_nonneg_right (by linarith) hJ.le)⟩
  refine ⟨Finset.sum_nonneg (fun i hi => (ht i hi).1), ?_⟩
  calc
    _ ≤ ∑ _i ∈ Finset.range (b - a), 2 * (b : ℝ) / J := Finset.sum_le_sum (fun i hi => (ht i hi).2)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_sub hab]
      ring

theorem actual_gamma_difference_bounds (J : ℝ) (n d : ℕ) (hJ : 0 < J)
    (hn : Odd n) (hd : Even d)
    (hrange : 2 * (particleExponent (n + 2 * d) : ℝ) ≤ J) :
    |logGammaCorrection J (particleExponent (n + 2 * d)) - logGammaCorrection J (particleExponent n)| ≤
        8 * (d : ℝ) * ((n : ℝ) + d) ^ 3 / J ∧
      |logGammaCorrection J (particleExponent (n + 2 * d)) -
        2 * logGammaCorrection J (particleExponent (n + d)) + logGammaCorrection J (particleExponent n)| ≤
        6 * (d : ℝ) ^ 2 * ((n : ℝ) + d) ^ 2 / J := by
  obtain ⟨k, rfl⟩ := odd_iff_exists_bit1.mp hn
  obtain ⟨p, rfl⟩ := even_iff_exists_two_mul.mp hd
  let x : ℝ := (2 * k + 1 : ℕ) + (2 * p : ℕ)
  have hx : 0 < x := by dsimp [x]; positivity
  have hdR : 0 ≤ ((2 * p : ℕ) : ℝ) := Nat.cast_nonneg _
  have hleft : 2 * k + 1 + 2 * (2 * p) = 2 * (k + 2 * p) + 1 := by ring
  have hmid : 2 * k + 1 + 2 * p = 2 * (k + p) + 1 := by ring
  rw [hleft] at hrange ⊢
  rw [hmid]
  have hαr : (particleExponent (2 * (k + 2 * p) + 1) : ℝ) =
      ((x + (2 * p : ℕ)) ^ 2 - 1) / 2 := by
    rw [particleExponent_odd]
    dsimp [x]
    push_cast
    ring
  have hαl : (particleExponent (2 * k + 1) : ℝ) = ((x - (2 * p : ℕ)) ^ 2 - 1) / 2 := by
    rw [particleExponent_odd]
    dsimp [x]
    push_cast
    ring
  have hα : (particleExponent (2 * (k + 2 * p) + 1) : ℝ) ≤ 2 * x ^ 2 := by
    rw [hαr]
    have hh : ((2 * p : ℕ) : ℝ) ≤ x := by
      dsimp [x]
      exact le_add_of_nonneg_left (Nat.cast_nonneg _)
    nlinarith [sq_nonneg (x - ((2 * p : ℕ) : ℝ))]
  have halr : particleExponent (2 * k + 1) ≤ particleExponent (2 * (k + 2 * p) + 1) := by
    rw [particleExponent_odd, particleExponent_odd]
    nlinarith
  have hαdiff : (particleExponent (2 * (k + 2 * p) + 1) : ℝ) - particleExponent (2 * k + 1) =
      2 * ((2 * p : ℕ) : ℝ) * x := by rw [hαr, hαl]; ring
  have hfirst := model_gamma_block_bounds J _ _ hJ halr hrange
  have hsecond := odd_particle_gamma_curvature_bounds J k p hJ hrange
  dsimp only at hsecond
  refine ⟨?_, ?_⟩
  · rw [abs_of_nonneg hfirst.1]
    apply hfirst.2.trans
    rw [hαdiff]
    change 2 * (2 * ((2 * p : ℕ) : ℝ) * x) * (particleExponent (2 * (k + 2 * p) + 1) : ℝ) / J ≤
      8 * ((2 * p : ℕ) : ℝ) * x ^ 3 / J
    apply div_le_div_of_nonneg_right _ hJ.le
    have hh := mul_le_mul_of_nonneg_left hα (show 0 ≤ 4 * ((2 * p : ℕ) : ℝ) * x by positivity)
    nlinarith
  · rw [abs_of_nonneg hsecond.1]
    apply hsecond.2.trans
    change (2 * ((2 * p * (2 * k + p + 1) : ℕ) : ℝ) ^ 2 +
      2 * ((4 * p ^ 2 : ℕ) : ℝ) * (particleExponent (2 * (k + 2 * p) + 1) : ℝ)) / J ≤
        6 * ((2 * p : ℕ) : ℝ) ^ 2 * x ^ 2 / J
    apply div_le_div_of_nonneg_right _ hJ.le
    have hv : ((2 * p * (2 * k + p + 1) : ℕ) : ℝ) ≤ ((2 * p : ℕ) : ℝ) * x := by
      dsimp [x]; push_cast; nlinarith
    have hv0 : 0 ≤ ((2 * p * (2 * k + p + 1) : ℕ) : ℝ) := Nat.cast_nonneg _
    have hv2 := pow_le_pow_left₀ hv0 hv 2
    have hw : ((4 * p ^ 2 : ℕ) : ℝ) = ((2 * p : ℕ) : ℝ) ^ 2 := by push_cast; ring
    rw [hw]
    have hmul := mul_le_mul_of_nonneg_left hα (show 0 ≤ 2 * ((2 * p : ℕ) : ℝ) ^ 2 by positivity)
    nlinarith

end
end IsingBulk.AnisoF002.NegativeHT
