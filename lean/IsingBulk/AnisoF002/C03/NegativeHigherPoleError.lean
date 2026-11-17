import IsingBulk.AnisoF002.C03.NegativePhaseExpansion

/-!
# Higher moving-pole error from the complete phase equation

The full phase Taylor estimate and the previously constructed coarse pole
bound give exactly the cubic, quartic and squared-radius error scales in
frozen F002 (4.8).  This lemma retains complex displacements; its real
restriction has the literal quadratic form Q.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Set Filter
open scoped Topology BigOperators

def higherPoleErrorConstant (M a C : ℝ) : ℝ := M * (C ^ 2 + C + Real.pi + 1) / a

theorem coarse_error_budget {N C U Q D P₃ P₄ : ℝ}
    (hN : 0 < N) (hC : 0 ≤ C) (hU : 0 ≤ U) (hQ : 0 ≤ Q)
    (hP₃ : 0 ≤ P₃) (hP₄ : 0 ≤ P₄)
    (hcoarse : U ≤ C * Q / N) (hD : D ≤ Real.pi / N) :
    N * U ^ 2 + U * Q + D * P₃ + P₄ ≤
      (C ^ 2 + C + Real.pi + 1) * (P₃ / N + P₄ + Q ^ 2 / N) := by
  have h₁ : N * U ^ 2 ≤ C ^ 2 * (Q ^ 2 / N) := by
    calc
      N * U ^ 2 ≤ N * (C * Q / N) ^ 2 := by gcongr
      _ = _ := by field_simp
  have h₂ : U * Q ≤ C * (Q ^ 2 / N) := by
    calc
      U * Q ≤ (C * Q / N) * Q := mul_le_mul_of_nonneg_right hcoarse hQ
      _ = _ := by ring
  have h₃ : D * P₃ ≤ Real.pi * (P₃ / N) := by
    calc
      D * P₃ ≤ (Real.pi / N) * P₃ := mul_le_mul_of_nonneg_right hD hP₃
      _ = _ := by ring
  have hL₁ : C ^ 2 + C ≤ C ^ 2 + C + Real.pi + 1 := by linarith [Real.pi_pos]
  have hL₂ : Real.pi ≤ C ^ 2 + C + Real.pi + 1 := by nlinarith
  have hL₃ : 1 ≤ C ^ 2 + C + Real.pi + 1 := by nlinarith [Real.pi_pos]
  calc
    _ ≤ (C ^ 2 + C) * (Q ^ 2 / N) + Real.pi * (P₃ / N) + 1 * P₄ := by nlinarith
    _ ≤ (C ^ 2 + C + Real.pi + 1) * (Q ^ 2 / N) +
        (C ^ 2 + C + Real.pi + 1) * (P₃ / N) +
        (C ^ 2 + C + Real.pi + 1) * P₄ := by gcongr
    _ = _ := by ring

set_option maxHeartbeats 1000000 in
theorem higher_pole_error_of_phase_expansion
    (n : ℕ) (hn : 0 < n) (g : ℂ × ℂ → ℂ) (τ d t : ℂ) (v : Fin n → ℂ)
    (M a C : ℝ) (hM : 0 ≤ M) (ha : 0 < a) (hC : 0 ≤ C)
    (hc : a ≤ ‖phaseTemperatureDerivative g (τ, d)‖)
    (hphase : (∑ i, g (t, d + v i)) = (n : ℂ) * g (τ, d))
    (hcoarse : ‖t - τ‖ ≤ C * displacementSquare n v / (n : ℝ))
    (hd : ‖d‖ ≤ Real.pi / (n : ℝ))
    (hexpansion :
      ‖(∑ i, g (t, d + v i)) - (n : ℂ) * g (τ, d) -
        (n : ℂ) * phaseTemperatureDerivative g (τ, d) * (t - τ) -
        (angularJet 2 g (τ, d) / 2) * (∑ i, v i ^ 2)‖ ≤
        M * ((n : ℝ) * ‖t - τ‖ ^ 2 + ‖t - τ‖ * displacementSquare n v +
          ‖d‖ * (∑ i, ‖v i‖ ^ 3) + ∑ i, ‖v i‖ ^ 4)) :
    ‖t - τ + (angularJet 2 g (τ, d) / (2 * phaseTemperatureDerivative g (τ, d))) *
      ((∑ i, v i ^ 2) / (n : ℂ))‖ ≤
      higherPoleErrorConstant M a C / (n : ℝ) *
        ((∑ i, ‖v i‖ ^ 3) / (n : ℝ) + (∑ i, ‖v i‖ ^ 4) +
          displacementSquare n v ^ 2 / (n : ℝ)) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hcpos : 0 < ‖phaseTemperatureDerivative g (τ, d)‖ := ha.trans_le hc
  have hcne : phaseTemperatureDerivative g (τ, d) ≠ 0 := norm_pos_iff.mp hcpos
  let E : ℝ := (∑ i, ‖v i‖ ^ 3) / (n : ℝ) + (∑ i, ‖v i‖ ^ 4) +
    displacementSquare n v ^ 2 / (n : ℝ)
  let L : ℝ := C ^ 2 + C + Real.pi + 1
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hbudget := coarse_error_budget (P₃ := ∑ i, ‖v i‖ ^ 3) (P₄ := ∑ i, ‖v i‖ ^ 4)
    hnR hC (norm_nonneg (t - τ))
    (displacementSquare_nonneg n v) (by positivity) (by positivity) hcoarse hd
  have hbound : ‖(n : ℂ) * phaseTemperatureDerivative g (τ, d) * (t - τ) +
      (angularJet 2 g (τ, d) / 2) * (∑ i, v i ^ 2)‖ ≤ M * L * E := by
    have hh := hexpansion.trans (mul_le_mul_of_nonneg_left hbudget hM)
    rw [hphase] at hh
    have he : (n : ℂ) * g (τ, d) - (n : ℂ) * g (τ, d) -
        (n : ℂ) * phaseTemperatureDerivative g (τ, d) * (t - τ) -
        (angularJet 2 g (τ, d) / 2) * (∑ i, v i ^ 2) =
        -((n : ℂ) * phaseTemperatureDerivative g (τ, d) * (t - τ) +
          (angularJet 2 g (τ, d) / 2) * (∑ i, v i ^ 2)) := by ring
    rw [he, norm_neg] at hh
    simpa only [mul_assoc] using hh
  have heq : t - τ + (angularJet 2 g (τ, d) / (2 * phaseTemperatureDerivative g (τ, d))) *
      ((∑ i, v i ^ 2) / (n : ℂ)) =
      ((n : ℂ) * phaseTemperatureDerivative g (τ, d) * (t - τ) +
        (angularJet 2 g (τ, d) / 2) * (∑ i, v i ^ 2)) /
          ((n : ℂ) * phaseTemperatureDerivative g (τ, d)) := by
    field_simp
  rw [heq, norm_div, norm_mul, show ‖(n : ℂ)‖ = (n : ℝ) by simp]
  calc
    _ ≤ (M * L * E) / ((n : ℝ) * ‖phaseTemperatureDerivative g (τ, d)‖) :=
      div_le_div_of_nonneg_right hbound (by positivity)
    _ ≤ (M * L * E) / ((n : ℝ) * a) := by gcongr
    _ = _ := by dsimp [higherPoleErrorConstant, E, L]; ring

end
end IsingBulk.AnisoF002.NegativeHT
