import IsingBulk.AnisoF002.C03.RegularIsotropicMixedAttenuation

/-!
# Quantitative product gap on the actual mixed isotropic contour

Every physical root, the full smooth populations and the actual radial
parameter are retained. The attenuation constant precedes N and epsilon.
The product estimate therefore supplies the 1/N mixed gap for both signs
of the physical product kernel.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set
open scoped Topology BigOperators
open IsingBulk.AnisoF002.RegularTail

theorem complex_cos_norm_le_exp_abs_im (z : ℂ) :
    ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  have h := norm_add_le (Complex.exp (z * Complex.I)) (Complex.exp (-z * Complex.I))
  rw [← Complex.two_cos, norm_mul, Complex.norm_two, Complex.norm_exp, Complex.norm_exp] at h
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, mul_one,
    zero_sub, Complex.neg_re, Complex.neg_im, neg_neg] at h
  have h1 := Real.exp_le_exp.mpr (neg_le_abs z.im)
  have h2 := Real.exp_le_exp.mpr (le_abs_self z.im)
  linarith

theorem isotropicRadialParameter_norm_le_three (α ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ‖isotropicRadialParameter α ε‖ ≤ 3 := by
  have hnorm : ‖isotropicExteriorRadial α ε‖ = 1 + ε := by
    rw [isotropicExteriorRadial_norm, abs_of_pos (by linarith : 0 < 1 + ε)]
  have hinv : (1 + ε)⁻¹ ≤ (1 : ℝ) := by
    apply (inv_le_one₀ (by linarith : 0 < 1 + ε)).mpr
    linarith
  calc
    _ ≤ ‖isotropicExteriorRadial α ε‖ + ‖(isotropicExteriorRadial α ε)⁻¹‖ := norm_add_le _ _
    _ = 1 + ε + (1 + ε)⁻¹ := by rw [norm_inv, hnorm]
    _ ≤ 3 := by linarith

def mixedRootAttenuationConstant : ℝ := 1 / (2 * (3 + Real.exp 1) + 1) ^ 2

theorem mixedRootAttenuationConstant_pos : 0 < mixedRootAttenuationConstant := by
  unfold mixedRootAttenuationConstant
  positivity

def actualBalancedRootProduct {N : ℕ} (S : ℂ) (η τ : ℝ) (θ : Fin N → ℝ) : ℂ :=
  ∏ i, isotropicInteriorRoot (S, actualHomotopyAngle η τ 1 θ i)

theorem actual_balanced_dispersion_norm_bound {N : ℕ} (hN : 0 < N)
    (S : ℂ) (hS : ‖S‖ ≤ 3) (η : ℝ) {τ : ℝ} (hτ : τ ∈ Icc 0 1)
    (θ : Fin N → ℝ) (i : Fin N) :
    ‖isotropicDispersion (S, actualHomotopyAngle η τ 1 θ i)‖ ≤ 3 + Real.exp 1 := by
  have hdisp := actual_balanced_homotopy_displacement η τ 1 hτ.1 (by norm_num) θ
    (by simpa only [Fintype.card_fin] using hN) i
  have him : |(actualHomotopyAngle η τ 1 θ i).im| ≤ 1 := by
    have h := Complex.abs_im_le_norm (actualHomotopyAngle η τ 1 θ i - (θ i : ℂ))
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at h
    exact (h.trans hdisp).trans hτ.2
  exact (norm_sub_le S (Complex.cos (actualHomotopyAngle η τ 1 θ i))).trans
    (add_le_add hS ((complex_cos_norm_le_exp_abs_im _).trans (Real.exp_le_exp.mpr him)))

theorem actual_balanced_product_log_bound {N : ℕ} (hN : 0 < N)
    (S : ℂ) (hSi : 0 < S.im) (hSn : ‖S‖ ≤ 3) {η τ : ℝ}
    (hη : 0 < η) (hτ : τ ∈ Icc 0 1) (θ : Fin N → ℝ) :
    mixedRootAttenuationConstant *
      (N * S.im + (2 * η * τ / N) * actualUpperPopulation η θ * actualLowerPopulation η θ) ≤
        -Real.log ‖actualBalancedRootProduct S η τ θ‖ := by
  have hW (i : Fin N) : 0 < (isotropicDispersion (S, actualHomotopyAngle η τ 1 θ i)).im :=
    actual_balanced_homotopy_sheet S hSi η τ 1 hη hτ.1 zero_le_one θ i
  have hbound (i : Fin N) : mixedRootAttenuationConstant *
      (isotropicDispersion (S, actualHomotopyAngle η τ 1 θ i)).im ≤
        -Real.log ‖isotropicInteriorRoot (S, actualHomotopyAngle η τ 1 θ i)‖ := by
    have h := upperEdgeRoot_log_attenuation (hW i)
      (by positivity : 0 ≤ 3 + Real.exp 1) (actual_balanced_dispersion_norm_bound hN S hSn η hτ θ i)
    convert h using 1
    · dsimp [mixedRootAttenuationConstant]
      ring
    · rfl
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hbound i)
  rw [← Finset.mul_sum, Finset.sum_neg_distrib] at hsum
  have hprod : Real.log ‖actualBalancedRootProduct S η τ θ‖ =
      ∑ i, Real.log ‖isotropicInteriorRoot (S, actualHomotopyAngle η τ 1 θ i)‖ := by
    rw [actualBalancedRootProduct, norm_prod, Real.log_prod]
    intro i _
    exact (norm_pos_iff.mpr (isotropicInteriorRoot_ne_zero _)).ne'
  rw [← hprod] at hsum
  exact (mul_le_mul_of_nonneg_left (actual_balanced_total_dispersion_im_lower hN S hη hτ.1 θ)
    mixedRootAttenuationConstant_pos.le).trans hsum

theorem actual_mixed_product_log_gap {N : ℕ} (hN : 0 < N)
    (S : ℂ) (hSi : 0 < S.im) (hSn : ‖S‖ ≤ 3) {η τ : ℝ}
    (hη : 0 < η) (hτ : τ ∈ Icc 0 1) (θ : Fin N → ℝ)
    (hP : 1 / 4 ≤ actualUpperPopulation η θ)
    (hQ : 1 / 4 ≤ actualLowerPopulation η θ) :
    (mixedRootAttenuationConstant * η * τ / 8) / N ≤
      -Real.log ‖actualBalancedRootProduct S η τ θ‖ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hPQ : (1 / 16 : ℝ) ≤ actualUpperPopulation η θ * actualLowerPopulation η θ := by
    have hh := mul_le_mul hP hQ (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by linarith : 0 ≤ actualUpperPopulation η θ)
    norm_num at hh
    exact hh
  have hmul := mul_le_mul_of_nonneg_left hPQ
    (show 0 ≤ 2 * η * τ / (N : ℝ) from div_nonneg
      (mul_nonneg (by positivity) hτ.1) hN0.le)
  have hbase : (η * τ / 8) / N ≤
      N * S.im + (2 * η * τ / N) * actualUpperPopulation η θ * actualLowerPopulation η θ := by
    have hnSi := mul_nonneg hN0.le hSi.le
    have he : (2 * η * τ / (N : ℝ)) * (1 / 16) = (η * τ / 8) / N := by ring
    rw [he] at hmul
    nlinarith
  have h := mul_le_mul_of_nonneg_left hbase mixedRootAttenuationConstant_pos.le
  apply le_trans _ (actual_balanced_product_log_bound hN S hSi hSn hη hτ θ)
  convert h using 1
  ring

theorem actual_radial_mixed_product_log_gap {N : ℕ} (hN : 0 < N)
    (α ε : ℝ) (hα : 0 < α ∧ α < Real.pi) (hε : 0 < ε) (hε1 : ε ≤ 1)
    {η τ : ℝ} (hη : 0 < η) (hτ : τ ∈ Icc 0 1) (θ : Fin N → ℝ)
    (hP : 1 / 4 ≤ actualUpperPopulation η θ)
    (hQ : 1 / 4 ≤ actualLowerPopulation η θ) :
    (mixedRootAttenuationConstant * η * τ / 8) / N ≤
      -Real.log ‖actualBalancedRootProduct (isotropicRadialParameter α ε) η τ θ‖ :=
  actual_mixed_product_log_gap hN _ (isotropicRadialParameter_estimates α ε hα hε hε1).2.2.2.1
    (isotropicRadialParameter_norm_le_three α ε hε.le hε1) hη hτ θ hP hQ

end
end IsingBulk.AnisoF002.Isotropic
