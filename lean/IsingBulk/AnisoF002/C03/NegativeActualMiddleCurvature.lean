import IsingBulk.AnisoF002.C03.RegularModelCenteredEstimates
import IsingBulk.AnisoF002.C03.NegativeSelectionGates

/-!
# Uniform negative curvature of the actual model in the whole middle range

The exact analytic and factorial estimates apply simultaneously to every
particle index in the displayed window.  The gamma restriction and all
error-absorption conditions are derived from that window.  No model
finite-difference hypothesis is added.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section

theorem exists_actual_model_middle_curvature {B : ℂ → ℂ}
    (hB : AnalyticAt ℂ B 0) (hslit : B 0 ∈ Complex.slitPlane)
    (c : ℝ) {s : ℝ} (hs : 0 < s) (d : ℕ) (hd : Even d) (hdpos : 0 < d) :
    ∃ T : ℝ, 0 < T ∧ ∀ n j : ℕ, Odd n → T ≤ Real.log j →
      Real.log j ≤ (n : ℝ) + d → 8 * ((n : ℝ) + d) ^ 2 ≤ (j : ℝ) →
      actualModelLog B c s (n + 2 * d) j -
          2 * actualModelLog B c s (n + d) j + actualModelLog B c s n j ≤
        -((d : ℝ) ^ 2 / 2) * Real.log j := by
  obtain ⟨C, R, hC, hR, hmodel⟩ := actual_model_centered_estimates hB hslit c hs d hd hdpos
  let T : ℝ := max R (max 8 (4 * C + 1))
  refine ⟨T, hR.trans_le (le_max_left _ _), ?_⟩
  intro n j hn hT hlow hhigh
  let x : ℝ := (n : ℝ) + d
  have hRx : R ≤ x := (le_max_left _ _).trans (hT.trans hlow)
  have hlog8 : 8 ≤ Real.log j :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hT)
  have hlogC : 4 * C + 1 ≤ Real.log j :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hT)
  have hx8 : 8 ≤ x := hlog8.trans hlow
  have hx : 0 < x := by linarith
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hdpos
  have hd2 : 1 ≤ (d : ℝ) ^ 2 := by nlinarith
  have hx2 : x ≤ x ^ 2 := by nlinarith
  have hCscale : C ≤ (d : ℝ) ^ 2 * x ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hd2 (sq_nonneg x)
    nlinarith
  have hClog : 4 * C ≤ (d : ℝ) ^ 2 * Real.log j := by
    have hh := mul_le_mul_of_nonneg_right hd2 (show 0 ≤ Real.log j by linarith)
    nlinarith
  have hNj : x ^ 2 ≤ (j : ℝ) := by change 8 * x ^ 2 ≤ _ at hhigh; nlinarith [sq_nonneg x]
  have hright : ((n + 2 * d : ℕ) : ℝ) ≤ 2 * x := by
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    dsimp [x]
    push_cast
    nlinarith
  have hright0 : (0 : ℝ) ≤ ((n + 2 * d : ℕ) : ℝ) := Nat.cast_nonneg _
  have hright2 : (((n + 2 * d : ℕ) : ℝ)) ^ 2 ≤ 4 * x ^ 2 := by nlinarith
  have hα : (particleExponent (n + 2 * d) : ℝ) ≤ (((n + 2 * d : ℕ) : ℝ)) ^ 2 := by
    exact_mod_cast particleExponent_le_sq (n + 2 * d)
  have hgamma : 2 * (particleExponent (n + 2 * d) : ℝ) ≤ (j : ℝ) := by
    change 8 * x ^ 2 ≤ _ at hhigh
    nlinarith
  exact negative_curvature_of_exact_factor_error hC.le hx hNj hCscale hClog
    (hmodel n j hn hRx hgamma).2

end
end IsingBulk.AnisoF002.NegativeHT
