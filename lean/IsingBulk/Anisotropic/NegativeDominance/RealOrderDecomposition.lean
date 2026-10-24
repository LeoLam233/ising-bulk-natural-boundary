import IsingBulk.Anisotropic.NegativeDominance.ModelDecomposition

/-! The real-order extension used only to select integer Taylor orders.
At integer orders this is the logarithm of the exact complex main model. -/
namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section

def modelLogReal (Bn rootBn hn : ℂ) (s : ℝ) (n : ℕ) (j : ℝ) : ℝ :=
  modelOrderConstant Bn rootBn hn s n-j*Real.log (tau n)+gammaLogRealOrder (alpha n) j

theorem modelLogReal_nat (Bn rootBn hn : ℂ) (s : ℝ) (n j : ℕ)
    (hnpos : 0 < n) (hj : alpha n < j)
    (hB : Bn ≠ 0) (hr : rootBn ≠ 0) (hh : hn ≠ 0) (hs : s ≠ 0) :
    modelLogReal Bn rootBn hn s n j = Real.log ‖model Bn rootBn hn s n j‖ :=
  (log_norm_model_eq Bn rootBn hn s n j hnpos hj
    (modelPrefactor_ne_zero Bn rootBn hn s n hB hr hh hs hnpos)).symm

theorem modelLogReal_decomposition (B0 Bn rootBn hn : ℂ) (s : ℝ) (n : ℕ) (j : ℝ)
    (hnpos : 0 < n) (hnodd : Odd n) (hj : (alpha n : ℝ) < j)
    (hB : Bn ≠ 0) (hr : rootBn ≠ 0) (hh : hn ≠ 0) (hs : s ≠ 0)
    (hsq : rootBn^2 = Bn) :
    modelLogReal Bn rootBn hn s n j = entropyPart n +
      (alpha n : ℝ) * (modelQuadraticConstant B0 s - Real.log j) -
      j * Real.log (tau n) - (((n : ℝ) - 1) / 2) * Real.log Real.pi +
      modelAdditiveConstant B0 + gammaCorrection (alpha n) j + modelAnalyticError B0 Bn hn n := by
  unfold modelLogReal modelOrderConstant
  rw [log_norm_modelPrefactor Bn rootBn hn s n hB hr hh hs hnpos,
    log_norm_root_eq_half hsq, gammaLogRealOrder_eq_correction (alpha n) j hj]
  have ha := two_mul_alpha_add_one n hnodd
  have har : 2 * (alpha n : ℝ) + 1 = (n : ℝ)^2 := by exact_mod_cast (ha.trans (pow_two n).symm)
  unfold entropyPart particleLog modelQuadraticConstant modelAdditiveConstant modelAnalyticError
  push_cast
  have he : (alpha n : ℝ) = ((n : ℝ)^2 - 1) / 2 := by linarith
  rw [he]
  ring

end
end IsingBulk.Anisotropic.NegativeDominance
