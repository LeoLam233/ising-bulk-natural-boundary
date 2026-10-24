import IsingBulk.Anisotropic.NegativeDominance.OrderBalance
import IsingBulk.Anisotropic.NegativeDominance.ResonanceScale

/-! Identification of the exact model with its real derivative-order
interpolation. Complex phases remain in the exact model; only its norm is
interpolated when selecting an order. -/
namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section

def modelPrefactor (Bn rootBn hn : ℂ) (s : ℝ) (n : ℕ) : ℂ :=
  -(Real.rpow 2 (2 - (alpha n : ℝ)) : ℂ) * (Bn ^ alpha n / rootBn) *
    (factorialProduct n : ℂ) * (Real.rpow n ((alpha n : ℝ) - 3 / 2) : ℂ) /
    ((Real.rpow Real.pi (((n : ℝ) - 1) / 2) : ℂ) * (s : ℂ) ^ (2 * alpha n)) *
    hn ^ (-(alpha n : ℤ))

/-- Physical branch nonvanishing gives model-prefactor nonvanishing without
any shared-phase or real-positivity assumption on B or the Hessian. -/
theorem modelPrefactor_ne_zero (Bn rootBn hn : ℂ) (s : ℝ) (n : ℕ)
    (hB : Bn ≠ 0) (hroot : rootBn ≠ 0) (hh : hn ≠ 0) (hs : s ≠ 0) (hnpos : 0 < n) :
    modelPrefactor Bn rootBn hn s n ≠ 0 := by
  have hrpow (x y : ℝ) (hx : 0 < x) : (Real.rpow x y : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos hx y).ne'
  have hfac : (factorialProduct n : ℂ) ≠ 0 := by exact_mod_cast factorialProduct_ne_zero n
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  unfold modelPrefactor
  apply mul_ne_zero _ (zpow_ne_zero _ hh)
  apply div_ne_zero
  · exact mul_ne_zero
      (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (hrpow _ _ (by norm_num)))
        (div_ne_zero (pow_ne_zero _ hB) hroot)) hfac)
      (hrpow _ _ (by exact_mod_cast hnpos))
  · exact mul_ne_zero (hrpow _ _ Real.pi_pos) (pow_ne_zero _ hs')

def modelOrderConstant (Bn rootBn hn : ℂ) (s : ℝ) (n : ℕ) : ℝ :=
  Real.log ‖modelPrefactor Bn rootBn hn s n‖ + ((alpha n : ℝ) - 1) * Real.log (tau n)

theorem model_factor_order (Bn rootBn hn : ℂ) (s : ℝ) (n j : ℕ) :
    model Bn rootBn hn s n j = modelPrefactor Bn rootBn hn s n *
      (tau n : ℂ) ^ ((alpha n : ℤ) - j - 1) *
      (Real.Gamma ((j : ℝ) + 1 - alpha n) / Real.Gamma ((j : ℝ) + 1) : ℝ) := rfl

/-- Exact logarithmic real-order representation of the complex model norm. -/
theorem log_norm_model_eq (Bn rootBn hn : ℂ) (s : ℝ) (n j : ℕ)
    (hnpos : 0 < n) (hj : alpha n < j)
    (hp : modelPrefactor Bn rootBn hn s n ≠ 0) :
    Real.log ‖model Bn rootBn hn s n j‖ = modelOrderConstant Bn rootBn hn s n -
      (j : ℝ) * Real.log (tau n) + gammaLogRealOrder (alpha n) j := by
  have ht := tau_pos n hnpos
  have hg := model_gamma_pos n j (Nat.le_of_lt hj)
  rw [model_factor_order, norm_mul, norm_mul, norm_zpow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos ht, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hg,
    Real.log_mul (mul_ne_zero (norm_ne_zero_iff.mpr hp) (zpow_ne_zero _ ht.ne')) hg.ne',
    Real.log_mul (norm_ne_zero_iff.mpr hp) (zpow_ne_zero _ ht.ne'), Real.log_zpow,
    ← gammaLogRealOrder_eq_log_gamma (alpha n) j hj]
  unfold modelOrderConstant
  push_cast
  ring

/-- The balance function is exactly the difference of logarithms of two
model norms at every admissible integer order. -/
theorem orderBalance_eq_log_model_ratio
    (Bn rootBn hn Bm rootBm hm : ℂ) (s : ℝ) (n m b j : ℕ)
    (hnpos : 0 < n) (hmpos : 0 < m) (hab : alpha m = alpha n + b)
    (hj : alpha m < j)
    (hpn : modelPrefactor Bn rootBn hn s n ≠ 0)
    (hpm : modelPrefactor Bm rootBm hm s m ≠ 0) :
    orderBalance (modelOrderConstant Bm rootBm hm s m - modelOrderConstant Bn rootBn hn s n)
      (Real.log (tau n) - Real.log (tau m)) (alpha n) b j =
      Real.log ‖model Bm rootBm hm s m j‖ - Real.log ‖model Bn rootBn hn s n j‖ := by
  have hjn : alpha n < j := by omega
  rw [log_norm_model_eq Bm rootBm hm s m j hmpos hj hpm,
    log_norm_model_eq Bn rootBn hn s n j hnpos hjn hpn]
  unfold orderBalance
  rw [hab]
  ring

end
end IsingBulk.Anisotropic.NegativeDominance
