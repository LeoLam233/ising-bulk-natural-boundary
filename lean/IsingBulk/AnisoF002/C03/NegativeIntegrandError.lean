import IsingBulk.AnisoF002.C03.NegativeSmallPoleError
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Error of the complete pole integrand

This proves frozen (4.28) using the convergent local logarithm of the
actual relative pole error.  It compares full complex integrands before
integration, with no assumption about their phases or signs.
-/

namespace IsingBulk.AnisoF002.NegativeHT
noncomputable section

theorem complex_exp_sub_one_le_exp_norm (z : ℂ) :
    ‖Complex.exp z - 1‖ ≤ Real.exp ‖z‖ - 1 := by
  simpa using Complex.norm_exp_sub_sum_le_exp_norm_sub_sum z 1

set_option maxHeartbeats 1000000 in
theorem complete_pole_integrand_error (k : ℕ) (ell T T₀ : ℂ) (D : ℝ)
    (hD : 0 < D) (hmodel : D ≤ ‖T₀‖) (herr : ‖T - T₀‖ ≤ D / 4) :
    ‖Complex.exp ell / T ^ k - 1 / T₀ ^ k‖ ≤
      (Real.exp (‖ell‖ + 2 * (k : ℝ) * ‖T - T₀‖ / D) - 1) / D ^ k := by
  have hT₀ : T₀ ≠ 0 := norm_pos_iff.mp (hD.trans_le hmodel)
  let e : ℂ := (T - T₀) / T₀
  have heNorm : ‖e‖ ≤ ‖T - T₀‖ / D := by
    dsimp [e]
    rw [norm_div]
    gcongr
  have heSmall : ‖e‖ ≤ (1 / 4 : ℝ) := by
    apply heNorm.trans
    exact (div_le_iff₀ hD).mpr (by linarith)
  have he0 : 1 + e ≠ 0 := by
    intro hz
    have he : e = -1 := by linear_combination hz
    rw [he, norm_neg, norm_one] at heSmall
    norm_num at heSmall
  have heq : 1 + e = T / T₀ := by dsimp [e]; field_simp; ring
  have hT : T ≠ 0 := (div_ne_zero_iff.mp (heq ▸ he0)).1
  let L := Complex.log (1 + e)
  have hL : ‖L‖ ≤ 2 * ‖T - T₀‖ / D := by
    have hh := Complex.norm_log_one_add_half_le_self
      (show ‖e‖ ≤ (1 / 2 : ℝ) by linarith)
    change ‖L‖ ≤ (3 / 2 : ℝ) * ‖e‖ at hh
    calc
      ‖L‖ ≤ (3 / 2 : ℝ) * ‖e‖ := hh
      _ ≤ 2 * ‖e‖ := by nlinarith [norm_nonneg e]
      _ ≤ 2 * (‖T - T₀‖ / D) := mul_le_mul_of_nonneg_left heNorm (by norm_num)
      _ = _ := by ring
  let E : ℂ := ell - (k : ℂ) * L
  have hE : ‖E‖ ≤ ‖ell‖ + 2 * (k : ℝ) * ‖T - T₀‖ / D := by
    have hh := norm_sub_le ell ((k : ℂ) * L)
    rw [norm_mul, show ‖(k : ℂ)‖ = (k : ℝ) by simp] at hh
    have hmul := mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg k)
    calc
      ‖E‖ ≤ ‖ell‖ + (k : ℝ) * ‖L‖ := hh
      _ ≤ ‖ell‖ + (k : ℝ) * (2 * ‖T - T₀‖ / D) := add_le_add le_rfl hmul
      _ = _ := by ring
  have hfactor : Complex.exp ell / T ^ k - 1 / T₀ ^ k =
      (Complex.exp E - 1) / T₀ ^ k := by
    dsimp [E, L]
    rw [Complex.exp_sub, Complex.exp_nat_mul, Complex.exp_log he0, heq, div_pow]
    field_simp
  have hnum : ‖Complex.exp E - 1‖ ≤
      Real.exp (‖ell‖ + 2 * (k : ℝ) * ‖T - T₀‖ / D) - 1 :=
    (complex_exp_sub_one_le_exp_norm E).trans (sub_le_sub_right (Real.exp_le_exp.mpr hE) 1)
  have hnon : 0 ≤ Real.exp (‖ell‖ + 2 * (k : ℝ) * ‖T - T₀‖ / D) - 1 := by
    have hh : 0 ≤ ‖ell‖ + 2 * (k : ℝ) * ‖T - T₀‖ / D := by positivity
    exact sub_nonneg.mpr ((Real.exp_zero ▸ Real.exp_le_exp.mpr hh))
  rw [hfactor, norm_div, norm_pow]
  calc
    _ ≤ (Real.exp (‖ell‖ + 2 * (k : ℝ) * ‖T - T₀‖ / D) - 1) / ‖T₀‖ ^ k :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ _ := by gcongr

end
end IsingBulk.AnisoF002.NegativeHT
