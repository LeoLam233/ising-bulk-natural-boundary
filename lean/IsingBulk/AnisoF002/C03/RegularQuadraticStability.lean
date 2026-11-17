import IsingBulk.AnisoF002.C03.RegularQuadraticContinuation

/-!
# Quantitative stability of the prescribed reciprocal-root continuation

The root sign is fixed at the center. A coarse linear estimate suffices
for a protected c/N^6 disk and avoids an unnecessary sharp derivative
estimate. No principal physical branch is silently substituted.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set
open scoped Topology

theorem complex_sqrt_one_difference (z : ℂ) : ‖Complex.sqrt (1 + z) - 1‖ ≤ ‖z‖ := by
  let s := Complex.sqrt (1 + z)
  have hre : 0 ≤ s.re := by
    dsimp [s]
    rw [Complex.sqrt, Complex.cpow_inv_two_re]
    exact Real.sqrt_nonneg _
  have hs : s ^ 2 = 1 + z := by
    simpa only [s, Complex.sqrt] using Complex.cpow_ofNat_inv_pow (1 + z) 2
  have he : (s - 1) * (s + 1) = z := by linear_combination hs
  have hden : 1 ≤ ‖s + 1‖ := by
    have h := Complex.re_le_norm (s + 1)
    simp only [Complex.add_re, Complex.one_re] at h
    linarith
  have hn := congrArg norm he
  rw [norm_mul] at hn
  have hh := mul_le_mul_of_nonneg_left hden (norm_nonneg (s - 1))
  simpa only [mul_one, hn] using hh

theorem reciprocalRootContinuation_variation {W₀ r₀ : ℂ} (hd : W₀ - r₀ ≠ 0) (W : ℂ) :
    ‖reciprocalRootContinuation W₀ r₀ W - r₀‖ ≤
      ‖W - W₀‖ * (1 + (‖W‖ + ‖W₀‖) / ‖W₀ - r₀‖) := by
  let D := W₀ - r₀
  let e := (W ^ 2 - W₀ ^ 2) / D ^ 2
  have hD : 0 < ‖D‖ := norm_pos_iff.mpr hd
  have he : reciprocalRootContinuation W₀ r₀ W - r₀ =
      (W - W₀) - D * (Complex.sqrt (1 + e) - 1) := by
    dsimp [reciprocalRootContinuation, D, e]
    ring
  have hsq : W ^ 2 - W₀ ^ 2 = (W - W₀) * (W + W₀) := by ring
  have heNorm : ‖e‖ ≤ ‖W - W₀‖ * (‖W‖ + ‖W₀‖) / ‖D‖ ^ 2 := by
    dsimp only [e]
    rw [norm_div, hsq, norm_mul, norm_pow]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (norm_add_le W W₀)
      (norm_nonneg (W - W₀))) (sq_nonneg _)
  rw [he]
  apply (norm_sub_le _ _).trans
  rw [norm_mul]
  apply (add_le_add le_rfl (mul_le_mul_of_nonneg_left
    ((complex_sqrt_one_difference e).trans heNorm) (norm_nonneg D))).trans_eq
  field_simp
  ring

theorem reciprocal_root_discriminant_gap {W r : ℂ}
    (hp : r ^ 2 - 2 * W * r + 1 = 0) (hr : ‖r‖ ≤ 1) :
    ‖1 - r ^ 2‖ ≤ 2 * ‖W - r‖ := by
  have he : 1 - r ^ 2 = 2 * (W - r) * r := by linear_combination hp
  rw [he, norm_mul, norm_mul, Complex.norm_two]
  exact (mul_le_mul_of_nonneg_left hr (by positivity)).trans_eq (mul_one _)

theorem reciprocalRootContinuation_uniform_variation {W₀ r₀ : ℂ}
    (hp : r₀ ^ 2 - 2 * W₀ * r₀ + 1 = 0) (hr : ‖r₀‖ ≤ 1)
    {H c : ℝ} (hH : 0 ≤ H) (hW : ‖W₀‖ ≤ H) (hc : 0 < c)
    {N : ℕ} (hN : 0 < N) (hgap : c / N ≤ ‖1 - r₀ ^ 2‖)
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖reciprocalRootContinuation W₀ r₀ (W₀ + z) - r₀‖ ≤
      (1 + 2 * (2 * H + 1) / c) * N * ‖z‖ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hDgap : c / (2 * N) ≤ ‖W₀ - r₀‖ := by
    have hd := reciprocal_root_discriminant_gap hp hr
    have he : c / (2 * (N : ℝ)) = (c / N) / 2 := by ring
    rw [he]
    linarith
  have hDpos : 0 < ‖W₀ - r₀‖ := (by positivity : 0 < c / (2 * N)).trans_le hDgap
  have hv := reciprocalRootContinuation_variation (norm_pos_iff.mp hDpos) (W₀ + z)
  rw [add_sub_cancel_left] at hv
  have hWz : ‖W₀ + z‖ + ‖W₀‖ ≤ 2 * H + 1 := by
    have ht := norm_add_le W₀ z
    linarith
  have hratio : (‖W₀ + z‖ + ‖W₀‖) / ‖W₀ - r₀‖ ≤ (2 * (2 * H + 1) / c) * N := by
    apply (div_le_div₀ (by positivity) hWz (by positivity : 0 < c / (2 * N)) hDgap).trans_eq
    field_simp
  apply hv.trans
  have hh : 1 + (‖W₀ + z‖ + ‖W₀‖) / ‖W₀ - r₀‖ ≤
      (1 + 2 * (2 * H + 1) / c) * N := by nlinarith
  simpa only [mul_assoc, mul_comm ‖z‖] using mul_le_mul_of_nonneg_left hh (norm_nonneg z)

theorem reciprocalRootContinuation_analyticAt_of_slit (W₀ r₀ W : ℂ)
    (hslit : 1 + (W ^ 2 - W₀ ^ 2) / (W₀ - r₀) ^ 2 ∈ Complex.slitPlane) :
    AnalyticAt ℂ (reciprocalRootContinuation W₀ r₀) W := by
  have ha : AnalyticAt ℂ (fun z : ℂ =>
      1 + (z ^ 2 - W₀ ^ 2) / (W₀ - r₀) ^ 2) W :=
    analyticAt_const.add (((analyticAt_id.pow 2).sub analyticAt_const).div_const)
  have hs : AnalyticAt ℂ (fun z : ℂ =>
      Complex.sqrt (1 + (z ^ 2 - W₀ ^ 2) / (W₀ - r₀) ^ 2)) W := by
    simpa only [Complex.sqrt] using
      ha.cpow (g := fun _ : ℂ => (2⁻¹ : ℂ)) analyticAt_const hslit
  exact analyticAt_id.sub (analyticAt_const.mul hs)

end
end IsingBulk.AnisoF002.RegularTail.C03
