import IsingBulk.AnisoF002.C03.NegativeIntegerWindow
import IsingBulk.AnisoF002.NegativeHT.UniformCurvaturePhase

/-!
# Quantitative gates for the actual model's selected-order and middle windows

The half-order gamma range is automatic throughout the literal selected
integer interval.  The exact-factor error is also absorbed into negative
discrete curvature under explicit uniform window conditions.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section

theorem selected_window_gamma_range {n d j : ℕ}
    (ht : 24 ≤ Real.log ((n + d : ℕ) : ℝ))
    (hj : (((n + d : ℕ) : ℝ)) ^ 2 * Real.log ((n + d : ℕ) : ℝ) / 3 ≤ (j : ℝ)) :
    2 * particleExponent (n + 2 * d) ≤ j := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hx0 : (0 : ℝ) ≤ ((n + d : ℕ) : ℝ) := Nat.cast_nonneg _
  have hr0 : (0 : ℝ) ≤ ((n + 2 * d : ℕ) : ℝ) := Nat.cast_nonneg _
  have hrle : ((n + 2 * d : ℕ) : ℝ) ≤ 2 * ((n + d : ℕ) : ℝ) := by
    push_cast
    nlinarith
  have hrsq : (((n + 2 * d : ℕ) : ℝ)) ^ 2 ≤ 4 * (((n + d : ℕ) : ℝ)) ^ 2 := by
    nlinarith
  have hα : (particleExponent (n + 2 * d) : ℝ) ≤ (((n + 2 * d : ℕ) : ℝ)) ^ 2 := by
    exact_mod_cast particleExponent_le_sq (n + 2 * d)
  have hlog := mul_le_mul_of_nonneg_left ht (sq_nonneg (((n + d : ℕ) : ℝ)))
  have hresult : 2 * (particleExponent (n + 2 * d) : ℝ) ≤ (j : ℝ) := by nlinarith
  exact_mod_cast hresult

theorem integer_interval_gamma_range {n d j : ℕ}
    (hn : 1 ≤ n + d) (ht : 256 ≤ Real.log ((n + d : ℕ) : ℝ))
    (hj : selectionStart (n + d) ≤ j) :
    2 * particleExponent (n + 2 * d) ≤ j := by
  have hlo := (selection_integer_endpoint_bounds hn ht).1
  apply selected_window_gamma_range (by linarith)
  exact hlo.trans (by exact_mod_cast hj)

theorem negative_curvature_of_exact_factor_error {S C d N j : ℝ}
    (hC : 0 ≤ C) (hN : 0 < N) (hNj : N ^ 2 ≤ j)
    (hCscale : C ≤ d ^ 2 * N ^ 2) (hClog : 4 * C ≤ d ^ 2 * Real.log j)
    (herr : |S + d ^ 2 * (2 * j / N ^ 2 + Real.log j)| ≤
      C * (1 + N ^ 2 / j + j / N ^ 4)) :
    S ≤ -(d ^ 2 / 2) * Real.log j := by
  have hj : 0 < j := (sq_pos_of_pos hN).trans_le hNj
  have hratio : N ^ 2 / j ≤ 1 := (div_le_one hj).mpr hNj
  have hsmall := mul_le_mul_of_nonneg_left hratio hC
  have hlarge : C * (j / N ^ 4) ≤ d ^ 2 * (j / N ^ 2) := by
    calc
      _ ≤ (d ^ 2 * N ^ 2) * (j / N ^ 4) :=
        mul_le_mul_of_nonneg_right hCscale (div_nonneg hj.le (pow_nonneg hN.le 4))
      _ = _ := by field_simp
  have hnonneg : 0 ≤ d ^ 2 * (j / N ^ 2) :=
    mul_nonneg (sq_nonneg d) (div_nonneg hj.le (sq_nonneg N))
  have hu := (abs_le.mp herr).2
  have he : C * (1 + N ^ 2 / j + j / N ^ 4) ≤ 2 * C + d ^ 2 * (j / N ^ 2) := by
    calc
      _ = C + C * (N ^ 2 / j) + C * (j / N ^ 4) := by ring
      _ ≤ C + C + d ^ 2 * (j / N ^ 2) := by
        apply add_le_add
        · exact add_le_add le_rfl (by simpa only [mul_one] using hsmall)
        · exact hlarge
      _ = _ := by ring
  have hu' := hu.trans he
  rw [show d ^ 2 * (2 * j / N ^ 2 + Real.log j) =
    2 * (d ^ 2 * (j / N ^ 2)) + d ^ 2 * Real.log j by ring] at hu'
  rw [show -(d ^ 2 / 2) * Real.log j = -(d ^ 2 * Real.log j) / 2 by ring]
  linarith only [hu', hClog, hnonneg]

theorem crossing_overshoot_absorbed {K d N j : ℝ}
    (hd : 1 ≤ d) (hN : 0 < N)
    (hKN : K * d ≤ N) (hlog : 4 ≤ Real.log j) :
    K * d / N ≤ (d ^ 2 / 2 * Real.log j) / 2 := by
  have hr : K * d / N ≤ 1 := (div_le_one hN).mpr hKN
  have hd2 : 1 ≤ d ^ 2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hlog (sq_nonneg d)
  nlinarith

end
end IsingBulk.AnisoF002.NegativeHT
