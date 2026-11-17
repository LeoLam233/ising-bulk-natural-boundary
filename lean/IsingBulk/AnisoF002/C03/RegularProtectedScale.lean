import IsingBulk.AnisoF002.C03.RegularFiniteRootStability

/-!
# A protected parameter scale for all reciprocal roots

The radius is fixed before the particle number. The exponent six is a
proved coarse scale; its polynomial Cauchy cost is sufficient for the
complete factorial particle tail.
-/

namespace IsingBulk.AnisoF002.RegularTail.C03
noncomputable section
open Set
open scoped Topology BigOperators

theorem power_scaled_norm_le {N : ℕ} (hN : 0 < N) {ρ : ℝ} (_hρ : 0 ≤ ρ)
    {z : ℂ} (hz : ‖z‖ ≤ ρ / (N : ℝ) ^ 6) {k : ℕ} (hk : k ≤ 6) :
    (N : ℝ) ^ k * ‖z‖ ≤ ρ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hp : (N : ℝ) ^ k ≤ (N : ℝ) ^ 6 := pow_le_pow_right₀ hN1 hk
  have hh := mul_le_mul hp hz (norm_nonneg z) (by positivity : 0 ≤ (N : ℝ) ^ 6)
  exact hh.trans_eq (mul_div_cancel₀ ρ (pow_ne_zero 6 hN0.ne'))

theorem reciprocalRootContinuation_slit_of_scale {N : ℕ} (hN : 0 < N)
    {H c ρ : ℝ} (hH : 0 ≤ H) (hc : 0 < c) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hρc : 8 * (2 * H + 1) * ρ ≤ c ^ 2)
    {W r z : ℂ} (hp : r ^ 2 - 2 * W * r + 1 = 0)
    (hr : ‖r‖ ≤ 1) (hW : ‖W‖ ≤ H) (hgap : c / N ≤ ‖1 - r ^ 2‖)
    (hz : ‖z‖ ≤ ρ / (N : ℝ) ^ 6) :
    1 + ((W + z) ^ 2 - W ^ 2) / (W - r) ^ 2 ∈ Complex.slitPlane := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hz1 : ‖z‖ ≤ 1 := by
    have hh := power_scaled_norm_le hN hρ hz (k := 0) (by omega)
    simpa only [pow_zero, one_mul] using hh.trans hρ1
  have hD : c / (2 * N) ≤ ‖W - r‖ := by
    have hg := reciprocal_root_discriminant_gap hp hr
    have he : c / (2 * (N : ℝ)) = (c / N) / 2 := by ring
    rw [he]
    linarith
  have hDpos : 0 < ‖W - r‖ := (by positivity : 0 < c / (2 * N)).trans_le hD
  have hDsq : c ^ 2 / (4 * (N : ℝ) ^ 2) ≤ ‖W - r‖ ^ 2 := by
    have hh := (sq_le_sq₀ (by positivity : 0 ≤ c / (2 * N)) hDpos.le).mpr hD
    convert hh using 1
    ring
  have hnum : ‖(W + z) ^ 2 - W ^ 2‖ ≤ ‖z‖ * (2 * H + 1) := by
    rw [show (W + z) ^ 2 - W ^ 2 = z * ((W + z) + W) by ring, norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg z)
    have h1 := norm_add_le (W + z) W
    have h2 := norm_add_le W z
    linarith
  have he : ‖((W + z) ^ 2 - W ^ 2) / (W - r) ^ 2‖ ≤ 1 / 2 := by
    rw [norm_div, norm_pow]
    apply (div_le_div₀ (by positivity) hnum (by positivity : 0 < c ^ 2 / (4 * (N : ℝ) ^ 2)) hDsq).trans
    apply (div_le_iff₀ (by positivity : 0 < c ^ 2 / (4 * (N : ℝ) ^ 2))).mpr
    have hscaled := power_scaled_norm_le hN hρ hz (k := 2) (by omega)
    have hm := mul_le_mul_of_nonneg_left hscaled (by positivity : 0 ≤ 8 * (2 * H + 1))
    have hh : 8 * (2 * H + 1) * ((N : ℝ) ^ 2 * ‖z‖) ≤ c ^ 2 := hm.trans hρc
    rw [show (1 / 2 : ℝ) * (c ^ 2 / (4 * (N : ℝ) ^ 2)) = c ^ 2 / (8 * (N : ℝ) ^ 2) by ring]
    apply (le_div_iff₀ (by positivity : 0 < 8 * (N : ℝ) ^ 2)).mpr
    nlinarith
  apply Complex.mem_slitPlane_iff.mpr
  left
  have hre := (abs_le.mp (Complex.abs_re_le_norm (((W + z) ^ 2 - W ^ 2) / (W - r) ^ 2))).1
  simp only [Complex.add_re, Complex.one_re]
  linarith

theorem reciprocalRootContinuation_analytic_on_protected_disk {N : ℕ} (hN : 0 < N)
    {H c ρ : ℝ} (hH : 0 ≤ H) (hc : 0 < c) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hρc : 8 * (2 * H + 1) * ρ ≤ c ^ 2)
    {W r : ℂ} (hp : r ^ 2 - 2 * W * r + 1 = 0)
    (hr : ‖r‖ ≤ 1) (hW : ‖W‖ ≤ H) (hgap : c / N ≤ ‖1 - r ^ 2‖)
    {z : ℂ} (hz : ‖z‖ ≤ ρ / (N : ℝ) ^ 6) :
    AnalyticAt ℂ (fun t : ℂ => reciprocalRootContinuation W r (W + t)) z := by
  have ha := reciprocalRootContinuation_analyticAt_of_slit W r (W + z)
    (reciprocalRootContinuation_slit_of_scale hN hH hc hρ hρ1 hρc hp hr hW hgap hz)
  exact ha.comp (analyticAt_const.add analyticAt_id)

end
end IsingBulk.AnisoF002.RegularTail.C03
