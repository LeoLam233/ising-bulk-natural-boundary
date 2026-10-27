import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

/-! LT22 Section 10: the exact coercive quadratic model and the error
absorption used in Lemma 10.2. The actual Taylor expansion of the dispersion
product and its integral limit remain separately named obligations. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped BigOperators
open Complex

def quadraticDenominator (A B ε ρ : ℝ) : ℂ :=
  (A * ε : ℝ) - Complex.I * (B * ρ ^ 2 : ℝ)

theorem quadraticDenominator_coercive {A B ε ρ : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hε : 0 ≤ ε) :
    min A B / 2 * (ε + ρ ^ 2) ≤ ‖quadraticDenominator A B ε ρ‖ := by
  have hreal : (quadraticDenominator A B ε ρ).re = A * ε := by
    simp [quadraticDenominator, pow_two, Complex.mul_re, Complex.mul_im]
  have himag : (quadraticDenominator A B ε ρ).im = -(B * ρ ^ 2) := by
    simp [quadraticDenominator, pow_two, Complex.mul_re, Complex.mul_im]
  have hr := Complex.abs_re_le_norm (quadraticDenominator A B ε ρ)
  have hi := Complex.abs_im_le_norm (quadraticDenominator A B ε ρ)
  rw [hreal, abs_of_nonneg (mul_nonneg hA.le hε)] at hr
  rw [himag, abs_neg, abs_of_nonneg (mul_nonneg hB.le (sq_nonneg ρ))] at hi
  have ha := mul_le_mul_of_nonneg_right (min_le_left A B) hε
  have hb := mul_le_mul_of_nonneg_right (min_le_right A B) (sq_nonneg ρ)
  nlinarith

theorem denominator_coercive_after_remainder {A B ε ρ : ℝ} {E : ℂ}
    (hA : 0 < A) (hB : 0 < B) (hε : 0 ≤ ε)
    (hE : ‖E‖ ≤ min A B / 4 * (ε + ρ ^ 2)) :
    min A B / 4 * (ε + ρ ^ 2) ≤ ‖quadraticDenominator A B ε ρ + E‖ := by
  have hq := quadraticDenominator_coercive (ρ := ρ) hA hB hε
  have ht := norm_add_le (quadraticDenominator A B ε ρ + E) (-E)
  simp only [add_neg_cancel_right, norm_neg] at ht
  linarith

theorem cubic_remainder_absorption {C ε ε₀ ρ δ : ℝ}
    (hC : 0 ≤ C) (hε : 0 ≤ ε) (hε₀ : ε ≤ ε₀)
    (_hρ : 0 ≤ ρ) (hδ : ρ ≤ δ) :
    C * (ε ^ 2 + ε * ρ + ρ ^ 3) ≤ C * (ε₀ + δ) * (ε + ρ ^ 2) := by
  have h1 : ε ^ 2 ≤ ε₀ * ε := by nlinarith
  have h2 : ε * ρ ≤ δ * ε := by
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hδ hε
  have h3 : ρ ^ 3 ≤ δ * ρ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hδ (sq_nonneg ρ)]
  have he0 : 0 ≤ ε₀ := hε.trans hε₀
  have h4 : 0 ≤ ε₀ * ρ ^ 2 := mul_nonneg he0 (sq_nonneg ρ)
  have h : ε ^ 2 + ε * ρ + ρ ^ 3 ≤ (ε₀ + δ) * (ε + ρ ^ 2) := by nlinarith
  calc
    C * (ε ^ 2 + ε * ρ + ρ ^ 3) ≤ C * ((ε₀ + δ) * (ε + ρ ^ 2)) :=
      mul_le_mul_of_nonneg_left h hC
    _ = _ := by ring

theorem source_denominator_bound {N : ℕ} {d ε ε₀ ρ δ C : ℝ} {E : ℂ}
    (hN : 0 < N) (hd : 0 < d) (hC : 0 ≤ C)
    (hε : 0 ≤ ε) (hε₀ : ε ≤ ε₀) (hρ : 0 ≤ ρ) (hδ : ρ ≤ δ)
    (hsmall : C * (ε₀ + δ) ≤ min (2 * (N : ℝ)) d / 4)
    (hE : ‖E‖ ≤ C * (ε ^ 2 + ε * ρ + ρ ^ 3)) :
    min (2 * (N : ℝ)) d / 4 * (ε + ρ ^ 2) ≤
      ‖quadraticDenominator (2 * N) d ε ρ + E‖ := by
  apply denominator_coercive_after_remainder (by positivity) hd hε
  calc
    ‖E‖ ≤ C * (ε ^ 2 + ε * ρ + ρ ^ 3) := hE
    _ ≤ C * (ε₀ + δ) * (ε + ρ ^ 2) := cubic_remainder_absorption hC hε hε₀ hρ hδ
    _ ≤ _ := mul_le_mul_of_nonneg_right hsmall (by positivity)

theorem first_order_scale_exponent {N : ℝ} {k : ℝ} (hk : k = N ^ 2 / 2 - 1) :
    N * (N - 1) / 2 + (N - 1) / 2 - (k + 1) = -(1 / 2 : ℝ) := by
  rw [hk]
  ring

theorem lower_denominator_radial_exponent {N : ℝ} {k : ℝ} (hk : k = N ^ 2 / 2 - 1) :
    N ^ 2 - 2 - 2 * k = 0 := by
  rw [hk]
  ring

end
end IsingBulk.Preferred22
