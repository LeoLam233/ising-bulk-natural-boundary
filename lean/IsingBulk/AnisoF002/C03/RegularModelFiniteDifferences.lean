import IsingBulk.AnisoF002.C03.RegularModelCorrections
import IsingBulk.AnisoF002.C03.RegularModelFactorials
import IsingBulk.AnisoF002.C03.RegularModelGammaBounds
import IsingBulk.AnisoF002.C03.RegularModelElementaryPolynomial
import IsingBulk.AnisoF002.C03.NegativeActualOrderStep

/-!
# Finite differences of the actual first-winding model

Every term comes from the exact logarithm of the original model
coefficient.  The finite factorial rectangle cancels the polynomial-log
factor before the analytic and gamma remainders are estimated.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open scoped Topology

def modelFirstLinearConstant (C d : ℝ) : ℝ :=
  2 * d * (2 + 3 * d + 2 * Real.log 2) + 3 * d + d ^ 3 + 200 * d ^ 4 + C * d

def modelFirstOrderConstant (C d : ℝ) : ℝ := 100 * d ^ 3 + C * d

def modelSecondConstant (C d : ℝ) : ℝ :=
  d ^ 2 * Real.log 2 + 3 * d ^ 3 + 3 * d ^ 2 + 200 * d ^ 4 + C * d ^ 2

def modelSecondOrderConstant (C d : ℝ) : ℝ := 384 * d ^ 4 + C * d ^ 2

theorem actual_model_finite_differences {B : ℂ → ℂ} {c s C : ℝ} (n d j : ℕ)
    (hn : Odd n) (hd : Even d) (hs : 0 < s) (hj : 0 < j)
    (hstep : (d : ℝ) ≤ ((n : ℝ) + d) / 4)
    (hrange : 2 * (particleExponent (n + 2 * d) : ℝ) ≤ j)
    (hfactors : ∀ k ∈ ({n, n + d, n + 2 * d} : Finset ℕ),
      B (windingTau k : ℂ) ≠ 0 ∧ firstWindingCurvature k (B (windingTau k : ℂ)) c s ≠ 0)
    (hcorrection :
      |actualModelRemainder B c s (n + 2 * d) - actualModelRemainder B c s n| ≤
        C * (d : ℝ) * ((n : ℝ) + d) ∧
      |actualModelRemainder B c s (n + 2 * d) - 2 * actualModelRemainder B c s (n + d) +
        actualModelRemainder B c s n| ≤ C * (d : ℝ) ^ 2 ∧
      |actualTemperatureCorrection (n + 2 * d) - actualTemperatureCorrection n| ≤
        C * (d : ℝ) / ((n : ℝ) + d) ^ 3 ∧
      |actualTemperatureCorrection (n + 2 * d) - 2 * actualTemperatureCorrection (n + d) +
        actualTemperatureCorrection n| ≤ C * (d : ℝ) ^ 2 / ((n : ℝ) + d) ^ 4) :
    |actualModelLog B c s (n + 2 * d) j - actualModelLog B c s n j -
      2 * (d : ℝ) * (2 * (j : ℝ) / ((n : ℝ) + d) - ((n : ℝ) + d) * Real.log j)| ≤
        modelFirstLinearConstant C d * ((n : ℝ) + d) + 8 * (d : ℝ) * ((n : ℝ) + d) ^ 3 / j +
          modelFirstOrderConstant C d * (j : ℝ) / ((n : ℝ) + d) ^ 3 ∧
      |actualModelLog B c s (n + 2 * d) j - 2 * actualModelLog B c s (n + d) j + actualModelLog B c s n j +
        (d : ℝ) ^ 2 * (2 * (j : ℝ) / ((n : ℝ) + d) ^ 2 + Real.log j)| ≤
          modelSecondConstant C d + 6 * (d : ℝ) ^ 2 * ((n : ℝ) + d) ^ 2 / j +
            modelSecondOrderConstant C d * (j : ℝ) / ((n : ℝ) + d) ^ 4 := by
  let x : ℝ := (n : ℝ) + d
  have hx1 : 1 ≤ x := by
    have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast hn.pos
    dsimp [x]
    linarith [show (0 : ℝ) ≤ d from Nat.cast_nonneg d]
  have hx : 0 < x := lt_of_lt_of_le (by norm_num) hx1
  have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  have hm : Odd (n + d) := hn.add_even hd
  have hp : Odd (n + 2 * d) := hn.add_even (even_two_mul d)
  have hal : particleExponent n ≤ j := by
    have hmono : (particleExponent n : ℝ) ≤ particleExponent (n + 2 * d) :=
      by exact_mod_cast (particleExponent_mono (show n ≤ n + 2 * d by omega))
    exact_mod_cast (show (particleExponent n : ℝ) ≤ j by linarith [show (0 : ℝ) ≤ particleExponent (n + 2 * d) from Nat.cast_nonneg _])
  have ham : particleExponent (n + d) ≤ j := by
    have hmono : (particleExponent (n + d) : ℝ) ≤ particleExponent (n + 2 * d) :=
      by exact_mod_cast (particleExponent_mono (show n + d ≤ n + 2 * d by omega))
    exact_mod_cast (show (particleExponent (n + d) : ℝ) ≤ j by linarith [show (0 : ℝ) ≤ particleExponent (n + 2 * d) from Nat.cast_nonneg _])
  have hap : particleExponent (n + 2 * d) ≤ j := by
    exact_mod_cast (show (particleExponent (n + 2 * d) : ℝ) ≤ j by linarith [show (0 : ℝ) ≤ particleExponent (n + 2 * d) from Nat.cast_nonneg _])
  have hlcast : (n : ℝ) = x - d := by dsimp [x]; ring
  have hmcast : ((n + d : ℕ) : ℝ) = x := by push_cast; rfl
  have hpcast : ((n + 2 * d : ℕ) : ℝ) = x + d := by dsimp [x]; push_cast; ring
  have hdec (k : ℕ) (hk : Odd k) (hkj : particleExponent k ≤ j)
      (hkf : k ∈ ({n, n + d, n + 2 * d} : Finset ℕ)) :
      actualModelLog B c s k j = Real.log (factorialProduct k) + 2 * (j : ℝ) * Real.log k +
        realModelElementary k - (particleExponent k : ℝ) * Real.log j - (j : ℝ) * Real.log (Real.pi ^ 2 / 2) +
        actualModelRemainder B c s k - (j : ℝ) * actualTemperatureCorrection k +
        logGammaCorrection (j : ℝ) (particleExponent k) := by
    rw [actualModelLog_exact_decomposition c s k j hk (hfactors k hkf).1 (hfactors k hkf).2 hs hj hkj]
    dsimp [realModelElementary, actualTemperatureCorrection]
    ring
  have hdl := hdec n hn hal (by simp)
  have hdm := hdec (n + d) hm ham (by simp)
  have hdp := hdec (n + 2 * d) hp hap (by simp)
  have ha1 : (particleExponent (n + 2 * d) : ℝ) - particleExponent n = 2 * (d : ℝ) * x := by
    rw [particleExponent_real_odd hp, particleExponent_real_odd hn, hpcast, hlcast]
    ring
  have ha2 : (particleExponent (n + 2 * d) : ℝ) - 2 * particleExponent (n + d) + particleExponent n =
      (d : ℝ) ^ 2 := by
    rw [particleExponent_real_odd hp, particleExponent_real_odd hm, particleExponent_real_odd hn,
      hpcast, hmcast, hlcast]
    ring
  let P₁ := Real.log (factorialProduct (n + 2 * d)) - Real.log (factorialProduct n) - 2 * (d : ℝ) * x * Real.log x
  let P₂ := Real.log (factorialProduct (n + 2 * d)) - 2 * Real.log (factorialProduct (n + d)) +
    Real.log (factorialProduct n) - (d : ℝ) ^ 2 * Real.log x
  let G₁ := realModelElementary (x + d) - realModelElementary (x - d) + 2 * (d : ℝ) * x * Real.log x
  let G₂ := realModelElementary (x + d) - 2 * realModelElementary x + realModelElementary (x - d) +
    (d : ℝ) ^ 2 * Real.log x
  let T₁ := 2 * (j : ℝ) * (Real.log (x + d) - Real.log (x - d) - 2 * (d : ℝ) / x)
  let T₂ := 2 * (j : ℝ) * (Real.log (x + d) - 2 * Real.log x + Real.log (x - d) + (d : ℝ) ^ 2 / x ^ 2)
  let R₁ := actualModelRemainder B c s (n + 2 * d) - actualModelRemainder B c s n
  let R₂ := actualModelRemainder B c s (n + 2 * d) - 2 * actualModelRemainder B c s (n + d) + actualModelRemainder B c s n
  let E₁ := -(j : ℝ) * (actualTemperatureCorrection (n + 2 * d) - actualTemperatureCorrection n)
  let E₂ := -(j : ℝ) * (actualTemperatureCorrection (n + 2 * d) - 2 * actualTemperatureCorrection (n + d) + actualTemperatureCorrection n)
  let H₁ := logGammaCorrection (j : ℝ) (particleExponent (n + 2 * d)) - logGammaCorrection (j : ℝ) (particleExponent n)
  let H₂ := logGammaCorrection (j : ℝ) (particleExponent (n + 2 * d)) -
    2 * logGammaCorrection (j : ℝ) (particleExponent (n + d)) + logGammaCorrection (j : ℝ) (particleExponent n)
  have hP₁ : |P₁| ≤ 2 * (d : ℝ) * (2 + 3 * (d : ℝ) + 2 * Real.log 2) * x := actual_factorial_first_difference n d hn.pos
  have hP₂ : |P₂| ≤ (d : ℝ) ^ 2 * Real.log 2 + 3 * (d : ℝ) ^ 3 := actual_factorial_second_difference n d hn.pos
  have hG := modelElementary_centered_bounds hx1 hd0 hstep
  have hT := model_log_centered_bounds hx hd0 hstep
  have hT₁ : |T₁| ≤ 100 * (d : ℝ) ^ 3 * (j : ℝ) / x ^ 3 := by
    dsimp [T₁]
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * (j : ℝ))]
    calc
      _ ≤ (2 * (j : ℝ)) * (50 * (d : ℝ) ^ 3 / x ^ 3) := mul_le_mul_of_nonneg_left hT.1 (by positivity)
      _ = _ := by ring
  have hT₂ : |T₂| ≤ 384 * (d : ℝ) ^ 4 * (j : ℝ) / x ^ 4 := by
    dsimp [T₂]
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * (j : ℝ))]
    calc
      _ ≤ (2 * (j : ℝ)) * (192 * (d : ℝ) ^ 4 / x ^ 4) := mul_le_mul_of_nonneg_left hT.2 (by positivity)
      _ = _ := by ring
  have hE₁ : |E₁| ≤ C * (d : ℝ) * (j : ℝ) / x ^ 3 := by
    dsimp [E₁]
    rw [abs_mul, abs_neg, abs_of_nonneg hj0]
    calc
      _ ≤ (j : ℝ) * (C * (d : ℝ) / x ^ 3) := mul_le_mul_of_nonneg_left hcorrection.2.2.1 hj0
      _ = _ := by ring
  have hE₂ : |E₂| ≤ C * (d : ℝ) ^ 2 * (j : ℝ) / x ^ 4 := by
    dsimp [E₂]
    rw [abs_mul, abs_neg, abs_of_nonneg hj0]
    calc
      _ ≤ (j : ℝ) * (C * (d : ℝ) ^ 2 / x ^ 4) := mul_le_mul_of_nonneg_left hcorrection.2.2.2 hj0
      _ = _ := by ring
  have hH := actual_gamma_difference_bounds (j : ℝ) n d (by exact_mod_cast hj) hn hd hrange
  have hR₁ : |R₁| ≤ C * (d : ℝ) * x := hcorrection.1
  have hR₂ : |R₂| ≤ C * (d : ℝ) ^ 2 := hcorrection.2.1
  have hsum (a b c d e f A B C D E F : ℝ) (ha : |a| ≤ A) (hb : |b| ≤ B) (hc : |c| ≤ C)
      (hd : |d| ≤ D) (he : |e| ≤ E) (hf : |f| ≤ F) :
      |a + b + c + d + e + f| ≤ A + B + C + D + E + F := by
    obtain ⟨ha₁, ha₂⟩ := abs_le.mp ha
    obtain ⟨hb₁, hb₂⟩ := abs_le.mp hb
    obtain ⟨hc₁, hc₂⟩ := abs_le.mp hc
    obtain ⟨hd₁, hd₂⟩ := abs_le.mp hd
    obtain ⟨he₁, he₂⟩ := abs_le.mp he
    obtain ⟨hf₁, hf₂⟩ := abs_le.mp hf
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hid1 : actualModelLog B c s (n + 2 * d) j - actualModelLog B c s n j -
      2 * (d : ℝ) * (2 * (j : ℝ) / x - x * Real.log j) = P₁ + G₁ + T₁ + R₁ + E₁ + H₁ := by
    rw [hdp, hdl]
    dsimp [P₁, G₁, T₁, R₁, E₁, H₁]
    rw [hpcast, hlcast]
    linear_combination -Real.log (j : ℝ) * ha1
  have hid2 : actualModelLog B c s (n + 2 * d) j - 2 * actualModelLog B c s (n + d) j + actualModelLog B c s n j +
      (d : ℝ) ^ 2 * (2 * (j : ℝ) / x ^ 2 + Real.log j) = P₂ + G₂ + T₂ + R₂ + E₂ + H₂ := by
    rw [hdp, hdm, hdl]
    dsimp [P₂, G₂, T₂, R₂, E₂, H₂]
    rw [hpcast, hmcast, hlcast]
    linear_combination -Real.log (j : ℝ) * ha2
  constructor
  · rw [hid1]
    have hh := hsum _ _ _ _ _ _ _ _ _ _ _ _ hP₁ hG.1 hT₁ hR₁ hE₁ hH.1
    convert hh using 1
    dsimp [modelFirstLinearConstant, modelFirstOrderConstant]
    ring
  · rw [hid2]
    have hh := hsum _ _ _ _ _ _ _ _ _ _ _ _ hP₂ hG.2 hT₂ hR₂ hE₂ hH.2
    convert hh using 1
    dsimp [modelSecondConstant, modelSecondOrderConstant]
    ring

end
end IsingBulk.AnisoF002.NegativeHT
