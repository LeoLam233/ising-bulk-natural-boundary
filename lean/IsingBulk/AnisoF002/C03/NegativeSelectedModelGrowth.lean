import IsingBulk.AnisoF002.C03.RegularModelGrowth
import IsingBulk.AnisoF002.C03.NegativeActualIntegerSelection

/-!
# Growth of the actual model at the selected integer-order scale

The full finite-factor estimate implies a lower bound with leading term
`j log j - j log log j`.  The bound is uniform over the entire rounded
selection interval, and the actual complex model is proved nonzero before
its logarithm is exponentiated.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section
open Filter

theorem selected_scale_log_growth {n j L C A : ℝ}
    (hn : 1 ≤ n) (ht : 256 ≤ Real.log n) (hC : 0 ≤ C)
    (hlo : n ^ 2 * Real.log n / 3 ≤ j)
    (hhi : j ≤ 3 * n ^ 2 * Real.log n / 2)
    (hmodel : |L - (2 * j * Real.log n - n ^ 2 / 2 * Real.log j - j * A)| ≤
      C * (n ^ 2 + n ^ 4 / j + j / n ^ 2)) :
    j * Real.log j - j * Real.log (Real.log j) -
      (Real.log 2 + 9 / 2 + A + 3 * C) * j ≤ L := by
  obtain ⟨hj, hsq, _⟩ := selection_scale_estimates hn ht hlo hhi
  have hn0 : 0 < n := by linarith
  have hnsq : n ≤ n ^ 2 := by nlinarith
  have hlogmono := Real.log_le_log hn0 (hnsq.trans hsq)
  have hlogj : 0 < Real.log j := by linarith
  have hlogn : 0 ≤ Real.log n := by linarith
  have hloghalf := log_le_half_of_pos hn0
  have hcubic : j ≤ n ^ 3 := by
    have hh := mul_le_mul_of_nonneg_left hloghalf (sq_nonneg n)
    nlinarith [pow_nonneg hn0.le 3]
  have hlogupper := Real.log_le_log hj hcubic
  rw [Real.log_pow] at hlogupper
  norm_num at hlogupper
  have hsmall : n ^ 2 / 2 * Real.log j ≤ 9 / 2 * j := by
    have hh := mul_le_mul_of_nonneg_left hlogupper (sq_nonneg n)
    nlinarith
  have hjupper : j ≤ 2 * n ^ 2 * Real.log j := by
    have hh := mul_le_mul_of_nonneg_left hlogmono (sq_nonneg n)
    nlinarith [mul_nonneg (sq_nonneg n) hlogn]
  have hloglower := Real.log_le_log hj hjupper
  rw [Real.log_mul (by positivity : 2 * n ^ 2 ≠ 0) hlogj.ne',
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (pow_ne_zero 2 hn0.ne'),
    Real.log_pow] at hloglower
  norm_num at hloglower
  have hlarge := mul_le_mul_of_nonneg_left hloglower hj.le
  have hfour : n ^ 4 / j ≤ n ^ 2 := by
    apply (div_le_iff₀ hj).mpr
    nlinarith [mul_le_mul_of_nonneg_left hsq (sq_nonneg n)]
  have hratio : j / n ^ 2 ≤ j := by
    apply div_le_self hj.le
    nlinarith
  have herr := mul_le_mul_of_nonneg_left
    (show n ^ 2 + n ^ 4 / j + j / n ^ 2 ≤ 3 * j by linarith) hC
  have hleft := (abs_le.mp hmodel).1
  nlinarith

theorem exists_actual_selected_model_growth {B : ℂ → ℂ}
    (hB : AnalyticAt ℂ B 0) (hslit : B 0 ∈ Complex.slitPlane)
    (c : ℝ) {s : ℝ} (hs : 0 < s) :
    ∃ D R : ℝ, 0 < D ∧ 0 < R ∧ ∀ n j : ℕ, Odd n → R ≤ (n : ℝ) →
      (n : ℝ) ^ 2 * Real.log n / 3 ≤ (j : ℝ) →
      (j : ℝ) ≤ 3 * (n : ℝ) ^ 2 * Real.log n / 2 →
      (j : ℝ) * Real.log j - (j : ℝ) * Real.log (Real.log j) - D * j ≤
        actualModelLog B c s n j ∧
      Real.exp ((j : ℝ) * Real.log j - (j : ℝ) * Real.log (Real.log j) - D * j) ≤
        ‖modelCoefficient n j (B (windingTau n : ℂ))
          (firstWindingCurvature n (B (windingTau n : ℂ)) c s) s (windingTau n)‖ := by
  obtain ⟨C, R₀, hC, hR₀, hmodel⟩ := actual_model_log_growth hB hslit c hs
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_actual_model_factors_ne_zero hB.continuousAt (Complex.slitPlane_ne_zero hslit) c s)
  let D : ℝ := Real.log 2 + 9 / 2 + |Real.log (Real.pi ^ 2 / 2)| + 3 * C + 1
  let R : ℝ := max R₀ (max (N : ℝ) (max 1 (Real.exp 256)))
  have hD : 0 < D := by
    have hh : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    dsimp [D]
    positivity
  refine ⟨D, R, hD, hR₀.trans_le (le_max_left _ _), ?_⟩
  intro n j hn hlarge hlo hhi
  have hR₀n : R₀ ≤ (n : ℝ) := (le_max_left _ _).trans hlarge
  have hNn : N ≤ n := by
    exact_mod_cast ((le_max_left _ _).trans ((le_max_right _ _).trans hlarge))
  have hn1 : 1 ≤ (n : ℝ) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hlarge))
  have hExp : Real.exp 256 ≤ (n : ℝ) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hlarge))
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn.pos
  have ht : 256 ≤ Real.log n := (Real.le_log_iff_exp_le hn0).mpr hExp
  have hscale := selection_scale_estimates hn1 ht hlo hhi
  have hgamma : 2 * (particleExponent n : ℝ) ≤ (j : ℝ) := by
    rw [particleExponent_real_odd hn]
    linarith [hscale.2.1]
  have hbound := selected_scale_log_growth hn1 ht hC.le hlo hhi
    (hmodel n j hn hR₀n hgamma)
  have hconst : Real.log 2 + 9 / 2 + Real.log (Real.pi ^ 2 / 2) + 3 * C ≤ D := by
    dsimp [D]
    linarith [le_abs_self (Real.log (Real.pi ^ 2 / 2))]
  have hconstj := mul_le_mul_of_nonneg_right hconst (Nat.cast_nonneg j)
  have hfinal : (j : ℝ) * Real.log j - (j : ℝ) * Real.log (Real.log j) - D * j ≤
      actualModelLog B c s n j := by linarith
  refine ⟨hfinal, ?_⟩
  have hf := hN n hNn
  have hnonzero := modelCoefficient_ne_zero n j (B (windingTau n : ℂ))
    (firstWindingCurvature n (B (windingTau n : ℂ)) c s) s (windingTau n)
    hn.pos hf.2.1 hf.2.2 hs (windingTau_pos n hn.pos)
  have he := Real.exp_le_exp.mpr hfinal
  simpa only [actualModelLog, Real.exp_log (norm_pos_iff.mpr hnonzero)] using he

end
end IsingBulk.AnisoF002.NegativeHT
