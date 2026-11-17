import IsingBulk.AnisoF002.C03.RegularIsotropicMixedGap

/-!
# The complete product kernel on the actual mixed contour

The literal product gap gives a uniform linear particle cost, for either
physical sign and in fact every sigma of norm at most one. The constants
precede the particle number and the radial approach parameter.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set
open scoped Topology BigOperators

theorem one_sub_norm_of_log_gap {z : ℂ} (hz : z ≠ 0) {g : ℝ} (hg : 0 < g)
    {N : ℕ} (hN : 0 < N) (hgap : g / N ≤ -Real.log ‖z‖) :
    g / ((1 + g) * N) ≤ 1 - ‖z‖ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hlog : Real.log ‖z‖ ≤ -(g / N) := by linarith
  have hnorm : ‖z‖ ≤ Real.exp (-(g / N)) := (Real.log_le_iff_le_exp hz0).mp hlog
  have hexp : 1 + g / N ≤ Real.exp (g / N) := by
    simpa only [add_comm] using Real.add_one_le_exp (g / N)
  have hden : 0 < 1 + g / N := by positivity
  have hinv : Real.exp (-(g / N)) ≤ (1 + g / N)⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ hden hexp
  have hmul : ‖z‖ * (1 + g / N) ≤ 1 := by
    exact (mul_le_mul_of_nonneg_right (hnorm.trans hinv) hden.le).trans_eq
      (inv_mul_cancel₀ hden.ne')
  have hsmall : g / N ≤ g := (div_le_self hg.le hN1)
  have hnorm1 : ‖z‖ ≤ 1 := by nlinarith [norm_nonneg z, div_pos hg hN0]
  apply (div_le_iff₀ (mul_pos (by positivity : 0 < 1 + g) hN0)).mpr
  have hbase : g / N ≤ (1 - ‖z‖) * (1 + g / N) := by nlinarith
  have hup := mul_le_mul_of_nonneg_left (show 1 + g / N ≤ 1 + g by linarith)
    (sub_nonneg.mpr hnorm1)
  have hh := mul_le_mul_of_nonneg_right (hbase.trans hup) hN0.le
  have he : (g / (N : ℝ)) * N = g := div_mul_cancel₀ g hN0.ne'
  rw [he] at hh
  nlinarith

theorem product_kernel_norm_of_log_gap {z σ : ℂ} (hz : z ≠ 0)
    (hσ : ‖σ‖ ≤ 1) {g : ℝ} (hg : 0 < g) {N : ℕ} (hN : 0 < N)
    (hgap : g / N ≤ -Real.log ‖z‖) :
    1 - σ * z ≠ 0 ∧ ‖(1 + σ * z) / (1 - σ * z)‖ ≤ (2 * (1 + g) / g) * N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hd0 : 0 < g / ((1 + g) * N) := by positivity
  have hd := one_sub_norm_of_log_gap hz hg hN hgap
  have hz1 : ‖z‖ < 1 := by linarith
  have hsz : ‖σ * z‖ ≤ ‖z‖ := by
    rw [norm_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hσ (norm_nonneg z)
  have hden : g / ((1 + g) * N) ≤ ‖1 - σ * z‖ := by
    have hrev := norm_sub_norm_le (1 : ℂ) (σ * z)
    rw [norm_one] at hrev
    linarith
  have hdz : 1 - σ * z ≠ 0 := norm_pos_iff.mp (hd0.trans_le hden)
  refine ⟨hdz, ?_⟩
  rw [norm_div]
  apply (div_le_iff₀ (norm_pos_iff.mpr hdz)).mpr
  have hnum : ‖1 + σ * z‖ ≤ 2 := by
    have ha := norm_add_le (1 : ℂ) (σ * z)
    rw [norm_one] at ha
    linarith
  have hb := mul_le_mul_of_nonneg_left hden
    (show 0 ≤ (2 * (1 + g) / g) * N by positivity)
  have he : ((2 * (1 + g) / g) * (N : ℝ)) * (g / ((1 + g) * N)) = 2 := by
    field_simp
  exact hnum.trans (by simpa only [he] using hb)

theorem actual_mixed_product_kernel_bound {N : ℕ} (hN : 0 < N)
    (S : ℂ) (hSi : 0 < S.im) (hSn : ‖S‖ ≤ 3) {η τ : ℝ}
    (hη : 0 < η) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (θ : Fin N → ℝ)
    (hP : 1 / 4 ≤ actualUpperPopulation η θ)
    (hQ : 1 / 4 ≤ actualLowerPopulation η θ) {σ : ℂ} (hσ : ‖σ‖ ≤ 1) :
    1 - σ * actualBalancedRootProduct S η τ θ ≠ 0 ∧
      ‖(1 + σ * actualBalancedRootProduct S η τ θ) /
        (1 - σ * actualBalancedRootProduct S η τ θ)‖ ≤
        (2 * (1 + mixedRootAttenuationConstant * η * τ / 8) /
          (mixedRootAttenuationConstant * η * τ / 8)) * N := by
  apply product_kernel_norm_of_log_gap
    (Finset.prod_ne_zero_iff.mpr (fun i _ => isotropicInteriorRoot_ne_zero _)) hσ
    (by positivity [mixedRootAttenuationConstant_pos]) hN
  exact actual_mixed_product_log_gap hN S hSi hSn hη ⟨hτ.le, hτ1⟩ θ hP hQ

end
end IsingBulk.AnisoF002.Isotropic
