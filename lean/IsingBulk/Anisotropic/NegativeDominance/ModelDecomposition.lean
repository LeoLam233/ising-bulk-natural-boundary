import IsingBulk.Anisotropic.NegativeDominance.ModelLogarithm
import IsingBulk.Anisotropic.NegativeDominance.EntropyCancellation
import IsingBulk.Anisotropic.NegativeDominance.OddIndices

/-! Exact decomposition isolating the uniformly bounded analytic corrections
from the factors that drive particle-index concavity. -/
namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section

def modelQuadraticConstant (B0 : ℂ) (s : ℝ) : ℝ :=
  -Real.log 2 + Real.log ‖B0‖ - 2 * Real.log |s| + Real.log (Real.pi^2 / 2)

def modelAdditiveConstant (B0 : ℂ) : ℝ :=
  2 * Real.log 2 - Real.log ‖B0‖ / 2 - Real.log (Real.pi^2 / 2)

def modelAnalyticError (B0 Bn hn : ℂ) (n : ℕ) : ℝ :=
  ((alpha n : ℝ) - 1 / 2) * (Real.log ‖Bn‖ - Real.log ‖B0‖) -
    (alpha n : ℝ) * Real.log ‖hn‖ - ((alpha n : ℝ) - 1) *
      (Real.log (Real.pi^2 / 2) - 2 * Real.log n - Real.log (tau n))

theorem log_norm_model_decomposition (B0 Bn rootBn hn : ℂ) (s : ℝ) (n j : ℕ)
    (hnpos : 0 < n) (hnodd : Odd n) (hj : alpha n < j)
    (hB : Bn ≠ 0) (hr : rootBn ≠ 0) (hh : hn ≠ 0) (hs : s ≠ 0)
    (hsq : rootBn^2 = Bn) :
    Real.log ‖model Bn rootBn hn s n j‖ = entropyPart n +
      (alpha n : ℝ) * (modelQuadraticConstant B0 s - Real.log j) -
      (j : ℝ) * Real.log (tau n) - (((n : ℝ) - 1) / 2) * Real.log Real.pi +
      modelAdditiveConstant B0 + gammaCorrection (alpha n) j + modelAnalyticError B0 Bn hn n := by
  rw [log_norm_model_eq Bn rootBn hn s n j hnpos hj
    (modelPrefactor_ne_zero Bn rootBn hn s n hB hr hh hs hnpos)]
  unfold modelOrderConstant
  rw [log_norm_modelPrefactor Bn rootBn hn s n hB hr hh hs hnpos,
    log_norm_root_eq_half hsq, gammaLogRealOrder_eq_correction (alpha n) j (by exact_mod_cast hj)]
  have ha := two_mul_alpha_add_one n hnodd
  have har : 2 * (alpha n : ℝ) + 1 = (n : ℝ)^2 := by exact_mod_cast (ha.trans (pow_two n).symm)
  unfold entropyPart particleLog modelQuadraticConstant modelAdditiveConstant modelAnalyticError
  push_cast
  have he : (alpha n : ℝ) = ((n : ℝ)^2 - 1) / 2 := by linarith
  rw [he]
  ring

end
end IsingBulk.Anisotropic.NegativeDominance
