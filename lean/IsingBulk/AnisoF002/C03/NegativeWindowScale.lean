import IsingBulk.AnisoF002.C03.NegativePoleModelComparison

/-!
# Uniform order-window consequences for the complete pole estimate

All lower bounds are explicit.  The Gaussian radial error is absorbed
into the same `N / sqrt k` error whenever `log k ≤ N`; no asymptotic
claim for unrestricted orders is made.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section

theorem order_scale_bounds {N k X : ℝ} (hN : 0 < N) (hX : 0 ≤ X)
    (hk : (8 + 32 * X) ^ 2 * N ^ 2 ≤ k) :
    0 < k ∧ 0 ≤ N / Real.sqrt k ∧ N / Real.sqrt k ≤ 1 ∧
      (N / Real.sqrt k) ^ 2 = N ^ 2 / k ∧
      X * (N / Real.sqrt k) ≤ 1 / 32 ∧ 64 * N ^ 2 ≤ k := by
  have hD : 0 < 8 + 32 * X := by positivity
  have hk0 : 0 < k := (mul_pos (sq_pos_of_pos hD) (sq_pos_of_pos hN)).trans_le hk
  have hs := Real.sqrt_pos.mpr hk0
  have hδ : 0 ≤ N / Real.sqrt k := div_nonneg hN.le hs.le
  have hroot : (8 + 32 * X) * N ≤ Real.sqrt k :=
    Real.le_sqrt_of_sq_le (by simpa only [mul_pow] using hk)
  have hm : (8 + 32 * X) * (N / Real.sqrt k) ≤ 1 := by
    rw [← mul_div_assoc]
    exact (div_le_one hs).mpr hroot
  have hXδ : 0 ≤ X * (N / Real.sqrt k) := mul_nonneg hX hδ
  have hDsq : 64 ≤ (8 + 32 * X) ^ 2 := by nlinarith
  refine ⟨hk0, hδ, by nlinarith, ?_, by nlinarith, ?_⟩
  · rw [div_pow, Real.sq_sqrt hk0.le]
  · exact (mul_le_mul_of_nonneg_right hDsq (sq_nonneg N)).trans hk

theorem gaussian_radial_tail_le_order_scale {N k : ℝ}
    (hN : 2 ≤ N) (hk : 0 < k) (hlog : Real.log k ≤ N) :
    Real.exp (-N ^ 2 / 4) ≤ N / Real.sqrt k := by
  have hs := Real.sqrt_pos.mpr hk
  have he : -N ^ 2 / 4 ≤ -Real.log (Real.sqrt k) := by
    rw [Real.log_sqrt hk.le]
    nlinarith
  calc
    _ ≤ Real.exp (-Real.log (Real.sqrt k)) := Real.exp_le_exp.mpr he
    _ = 1 / Real.sqrt k := by rw [Real.exp_neg, Real.exp_log hs, one_div]
    _ ≤ N / Real.sqrt k := div_le_div_of_nonneg_right (by linarith) hs.le

theorem phase_factor_uniform_bound {N C : ℝ} (hN : 1 ≤ N) :
    Real.exp (2 * C ^ 2 / N ^ 2) ≤ Real.exp (2 * C ^ 2) := by
  apply Real.exp_le_exp.mpr
  have hN2 : 1 ≤ N ^ 2 := by nlinarith
  exact div_le_self (by positivity) hN2

end
end IsingBulk.AnisoF002.NegativeHT
