import IsingBulk.Anisotropic.NegativeDominance.ModelOrderInterface

/-! Exact expansion of the first-winding model logarithm into all the terms
needed for n-direction finite differences. No terms are discarded. -/
namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section

theorem log_norm_modelPrefactor (Bn rootBn hn : ℂ) (s : ℝ) (n : ℕ)
    (hB : Bn ≠ 0) (hr : rootBn ≠ 0) (hh : hn ≠ 0) (hs : s ≠ 0) (hnpos : 0 < n) :
    Real.log ‖modelPrefactor Bn rootBn hn s n‖ =
      (2 - (alpha n : ℝ)) * Real.log 2 +
      (alpha n : ℝ) * Real.log ‖Bn‖ - Real.log ‖rootBn‖ +
      Real.log (factorialProduct n) + ((alpha n : ℝ) - 3 / 2) * Real.log n -
      (((n : ℝ) - 1) / 2) * Real.log Real.pi -
      (2 * alpha n : ℕ) * Real.log |s| - (alpha n : ℝ) * Real.log ‖hn‖ := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hnpos
  have h2 : 0 < Real.rpow 2 (2 - (alpha n : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hnp : 0 < Real.rpow (n : ℝ) ((alpha n : ℝ) - 3 / 2) := Real.rpow_pos_of_pos hnr _
  have hpp : 0 < Real.rpow Real.pi (((n : ℝ) - 1) / 2) := Real.rpow_pos_of_pos Real.pi_pos _
  have hnB : ‖Bn‖ ≠ 0 := norm_ne_zero_iff.mpr hB
  have hnrB : ‖rootBn‖ ≠ 0 := norm_ne_zero_iff.mpr hr
  have hnh : ‖hn‖ ≠ 0 := norm_ne_zero_iff.mpr hh
  have hsa : |s| ≠ 0 := abs_ne_zero.mpr hs
  have hnBpos : 0 < ‖Bn‖ := norm_pos_iff.mpr hB
  have hnrootpos : 0 < ‖rootBn‖ := norm_pos_iff.mpr hr
  have hnhpos : 0 < ‖hn‖ := norm_pos_iff.mpr hh
  have hspos : 0 < |s| := abs_pos.mpr hs
  have hfpos := factorialProduct_pos n
  unfold modelPrefactor
  simp only [norm_mul, norm_div, norm_neg, norm_pow, norm_zpow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos h2, abs_of_pos hnp, abs_of_pos hpp,
    abs_of_pos (factorialProduct_pos n)]
  rw [Real.log_mul (by positivity) (by positivity)]
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_pow, Real.log_zpow]
  simp only [Real.rpow_eq_pow]
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2), Real.log_rpow hnr, Real.log_rpow Real.pi_pos]
  push_cast
  ring

/-- The norm identity follows from the physical square-root equation, so its
phase and sign never need to be replaced by an artificial positive root. -/
theorem log_norm_root_eq_half {B rootB : ℂ} (hsq : rootB^2 = B) :
    Real.log ‖rootB‖ = Real.log ‖B‖ / 2 := by
  have hh := congrArg (fun z : ℂ => Real.log ‖z‖) hsq
  rw [norm_pow, Real.log_pow] at hh
  norm_num at hh
  linarith

end
end IsingBulk.Anisotropic.NegativeDominance
