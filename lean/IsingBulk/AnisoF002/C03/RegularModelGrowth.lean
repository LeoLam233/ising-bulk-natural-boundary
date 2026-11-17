import IsingBulk.AnisoF002.C03.RegularModelCenteredEstimates
import IsingBulk.AnisoF002.C03.RegularModelFactorialGrowth
import IsingBulk.AnisoF002.C03.RegularModelCorrectionValues

/-!
# Uniform pointwise growth of the actual first-winding model

This is the literal logarithm of the original modelCoefficient at the
actual B(tau_n), curvature h_n and winding temperature.  All finite
factors and the half-unit exponent correction are retained before taking
the uniform bound.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Filter
open scoped Topology

theorem model_log_order_bound (n j : ℕ) (hn : 0 < n) (hj : 0 < j) :
    Real.log j ≤ 2 * (n : ℝ) ^ 2 + (j : ℝ) / (n : ℝ) ^ 2 := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hjR : 0 < (j : ℝ) := by exact_mod_cast hj
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have h := Real.log_le_sub_one_of_pos (div_pos hjR (sq_pos_of_pos hnR))
  rw [Real.log_div hjR.ne' (pow_ne_zero 2 hnR.ne'), Real.log_pow] at h
  have hlog := Real.log_le_sub_one_of_pos hnR
  nlinarith

theorem model_gamma_value_bound (n j : ℕ) (hn : Odd n) (hj : 0 < j)
    (hrange : 2 * (particleExponent n : ℝ) ≤ j) :
    |logGammaCorrection (j : ℝ) (particleExponent n)| ≤ 2 * (n : ℝ) ^ 4 / j := by
  have hjR : 0 < (j : ℝ) := by exact_mod_cast hj
  have hh := model_gamma_block_bounds (j : ℝ) 0 (particleExponent n) hjR (Nat.zero_le _) hrange
  have hzero : logGammaCorrection (j : ℝ) 0 = 0 := by simp [logGammaCorrection]
  rw [hzero, sub_zero] at hh
  simp only [Nat.cast_zero, sub_zero] at hh
  rw [abs_of_nonneg hh.1]
  apply hh.2.trans
  apply div_le_div_of_nonneg_right _ hjR.le
  have hα : (particleExponent n : ℝ) ≤ (n : ℝ) ^ 2 := by
    rw [particleExponent_real_odd hn]
    nlinarith [sq_nonneg (n : ℝ)]
  have hpow := pow_le_pow_left₀ (show (0 : ℝ) ≤ particleExponent n from Nat.cast_nonneg _) hα 2
  nlinarith

theorem actual_model_log_growth {B : ℂ → ℂ} (hB : AnalyticAt ℂ B 0)
    (hslit : B 0 ∈ Complex.slitPlane) (c : ℝ) {s : ℝ} (hs : 0 < s) :
    ∃ C R : ℝ, 0 < C ∧ 0 < R ∧ ∀ n j : ℕ, Odd n → R ≤ (n : ℝ) →
      2 * (particleExponent n : ℝ) ≤ j →
      |actualModelLog B c s n j -
        (2 * (j : ℝ) * Real.log n - (n : ℝ) ^ 2 / 2 * Real.log j - (j : ℝ) * Real.log (Real.pi ^ 2 / 2))| ≤
        C * ((n : ℝ) ^ 2 + (n : ℝ) ^ 4 / j + (j : ℝ) / (n : ℝ) ^ 2) := by
  obtain ⟨C₀, R₀, hC₀, hR₀, hcorr⟩ := actual_model_correction_values hB hslit c s
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_actual_model_factors_ne_zero hB.continuousAt (Complex.slitPlane_ne_zero hslit) c s)
  let R := max R₀ (max 3 (N : ℝ))
  let C := 6 + Real.log 2 + C₀
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hC : 0 < C := by dsimp [C]; positivity
  have hR : 0 < R := hR₀.trans_le (le_max_left _ _)
  refine ⟨C, R, hC, hR, ?_⟩
  intro n j hn hlarge hrange
  have hR₀n : R₀ ≤ (n : ℝ) := (le_max_left _ _).trans hlarge
  have hn3 : (3 : ℝ) ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hlarge)
  have hNn : N ≤ n := by exact_mod_cast ((le_max_right _ _).trans ((le_max_right _ _).trans hlarge))
  have hn1 : 1 ≤ (n : ℝ) := by linarith
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn.pos
  have hαpos : 0 < (particleExponent n : ℝ) := by
    rw [particleExponent_real_odd hn]
    nlinarith
  have hj : 0 < j := by exact_mod_cast (show (0 : ℝ) < j by linarith)
  have hjR : 0 < (j : ℝ) := by exact_mod_cast hj
  have hj1 : 1 ≤ (j : ℝ) := by exact_mod_cast hj
  have hαj : particleExponent n ≤ j := by exact_mod_cast (show (particleExponent n : ℝ) ≤ j by linarith)
  have hf := hN n hNn
  have hdec := actualModelLog_exact_decomposition c s n j hn hf.2.1 hf.2.2 hs hj hαj
  have hcv := hcorr n hn hR₀n
  have hP := actual_factorial_log_growth n hn.pos
  have hE := model_gamma_value_bound n j hn hj hrange
  have hlogn : |Real.log n| ≤ (n : ℝ) ^ 2 := by
    rw [abs_of_nonneg (Real.log_nonneg hn1)]
    have hh := Real.log_le_sub_one_of_pos hnR
    nlinarith
  have hlogj : |Real.log j / 2| ≤ (n : ℝ) ^ 2 + (j : ℝ) / (2 * (n : ℝ) ^ 2) := by
    rw [abs_of_nonneg (by positivity : 0 ≤ Real.log j / 2)]
    have hh := model_log_order_bound n j hn.pos hj
    rw [show (j : ℝ) / (2 * (n : ℝ) ^ 2) = ((j : ℝ) / (n : ℝ) ^ 2) / 2 by ring]
    linarith
  have htemp : |-(j : ℝ) * actualTemperatureCorrection n| ≤ C₀ * (j : ℝ) / (n : ℝ) ^ 2 := by
    rw [abs_mul, abs_neg, abs_of_pos hjR]
    calc
      _ ≤ (j : ℝ) * (C₀ / (n : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hcv.2 hjR.le
      _ = _ := by ring
  let P := Real.log (factorialProduct n) - (n : ℝ) ^ 2 / 2 * Real.log n
  let T := -(j : ℝ) * actualTemperatureCorrection n
  have hid : actualModelLog B c s n j -
      (2 * (j : ℝ) * Real.log n - (n : ℝ) ^ 2 / 2 * Real.log j - (j : ℝ) * Real.log (Real.pi ^ 2 / 2)) =
      P + Real.log n + Real.log j / 2 + actualModelRemainder B c s n + T +
        logGammaCorrection (j : ℝ) (particleExponent n) := by
    rw [hdec, particleExponent_real_odd hn]
    dsimp [P, T, actualTemperatureCorrection]
    ring
  rw [hid]
  have hsum : |P + Real.log n + Real.log j / 2 + actualModelRemainder B c s n + T +
      logGammaCorrection (j : ℝ) (particleExponent n)| ≤
      (2 + Real.log 2) * (n : ℝ) ^ 2 + (n : ℝ) ^ 2 +
      ((n : ℝ) ^ 2 + (j : ℝ) / (2 * (n : ℝ) ^ 2)) + C₀ * (n : ℝ) ^ 2 +
      C₀ * (j : ℝ) / (n : ℝ) ^ 2 + 2 * (n : ℝ) ^ 4 / j := by
    obtain ⟨hP₁, hP₂⟩ := abs_le.mp hP
    obtain ⟨hl₁, hl₂⟩ := abs_le.mp hlogn
    obtain ⟨hj₁, hj₂⟩ := abs_le.mp hlogj
    obtain ⟨hr₁, hr₂⟩ := abs_le.mp hcv.1
    obtain ⟨ht₁, ht₂⟩ := abs_le.mp htemp
    obtain ⟨he₁, he₂⟩ := abs_le.mp hE
    dsimp [P, T]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  apply hsum.trans
  have hcoeffn : 4 + Real.log 2 + C₀ ≤ C := by dsimp [C]; linarith
  have hcoefft : C₀ + 1 / 2 ≤ C := by dsimp [C]; linarith
  have hcoeffg : (2 : ℝ) ≤ C := by dsimp [C]; linarith
  calc
    _ = (4 + Real.log 2 + C₀) * (n : ℝ) ^ 2 + (C₀ + 1 / 2) * ((j : ℝ) / (n : ℝ) ^ 2) +
        2 * ((n : ℝ) ^ 4 / j) := by ring
    _ ≤ C * (n : ℝ) ^ 2 + C * ((j : ℝ) / (n : ℝ) ^ 2) + C * ((n : ℝ) ^ 4 / j) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_right hcoeffn (sq_nonneg _))
        (mul_le_mul_of_nonneg_right hcoefft (by positivity)))
        (mul_le_mul_of_nonneg_right hcoeffg (by positivity))
    _ = _ := by ring

end
end IsingBulk.AnisoF002.NegativeHT
