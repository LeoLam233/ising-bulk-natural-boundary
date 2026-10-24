import IsingBulk.Anisotropic.NegativeNormalForm.Algebra
import Mathlib.Analysis.Real.Sqrt

/-! The complex bilinear pole denominator along the actual straight homotopy.
These estimates do not replace the holomorphic-chain Stokes theorem. -/
namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open scoped BigOperators

/-- Hermitian squared length, used only for estimates. -/
def absoluteEnergy {n : ℕ} (v : Config n) : ℝ := ∑ i, ‖v i‖ ^ 2

theorem absoluteEnergy_nonneg {n : ℕ} (v : Config n) : 0 ≤ absoluteEnergy v := by
  unfold absoluteEnergy
  positivity

theorem norm_pairing_le {n : ℕ} (v w : Config n) :
    ‖pairing v w‖ ≤ Real.sqrt (absoluteEnergy v) * Real.sqrt (absoluteEnergy w) := by
  calc
    ‖pairing v w‖ ≤ ∑ i, ‖v i * w i‖ := norm_sum_le _ _
    _ = ∑ i, ‖v i‖ * ‖w i‖ := by simp only [norm_mul]
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun i => ‖v i‖) (fun i => ‖w i‖)

theorem norm_quadratic_le {n : ℕ} (v : Config n) :
    ‖quadratic v‖ ≤ absoluteEnergy v := by
  calc
    ‖quadratic v‖ ≤ ∑ i, ‖v i ^ 2‖ := norm_sum_le _ _
    _ = absoluteEnergy v := by simp only [norm_pow, absoluteEnergy]

theorem norm_quadratic_perturbation {n : ℕ} (v e : Config n) :
    ‖quadratic (fun i => v i + e i) - quadratic v‖ ≤
      2 * Real.sqrt (absoluteEnergy v) * Real.sqrt (absoluteEnergy e) + absoluteEnergy e := by
  have hq : quadratic (fun i => v i + e i) - quadratic v =
      2 * pairing v e + quadratic e := by
    have h := quadratic_add v e 1
    simp only [one_mul, one_pow] at h
    linear_combination h
  rw [hq]
  calc
    ‖2 * pairing v e + quadratic e‖ ≤ ‖2 * pairing v e‖ + ‖quadratic e‖ := norm_add_le _ _
    _ = 2 * ‖pairing v e‖ + ‖quadratic e‖ := by simp
    _ ≤ _ := by nlinarith [norm_pairing_le v e, norm_quadratic_le e]

theorem quadratic_real {n : ℕ} (v : Fin n → ℝ) :
    (quadratic (fun i => (v i : ℂ))).re = ∑ i, v i ^ 2 := by
  simp only [quadratic, Complex.re_sum, ← Complex.ofReal_pow, Complex.ofReal_re]

theorem absoluteEnergy_real {n : ℕ} (v : Fin n → ℝ) :
    absoluteEnergy (fun i => (v i : ℂ)) = ∑ i, v i ^ 2 := by
  simp [absoluteEnergy, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- A direct lower bound for the real part of the bilinear quadratic form,
with constants independent of the particle dimension. -/
theorem quadratic_real_perturbation_lower {n : ℕ} (v : Fin n → ℝ) (e : Config n)
    (eta : ℝ) (heta : 0 ≤ eta)
    (he : Real.sqrt (absoluteEnergy e) ≤ eta * Real.sqrt (∑ i, v i ^ 2)) :
    (1 - 2 * eta - eta ^ 2) * (∑ i, v i ^ 2) ≤
      (quadratic (fun i => (v i : ℂ) + e i)).re := by
  let q : ℝ := ∑ i, v i ^ 2
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hsq := Real.sq_sqrt hq
  have heq := Real.sq_sqrt (absoluteEnergy_nonneg e)
  have hp := norm_quadratic_perturbation (fun i => (v i : ℂ)) e
  rw [absoluteEnergy_real] at hp
  have hr := Complex.abs_re_le_norm
    (quadratic (fun i => (v i : ℂ) + e i) - quadratic (fun i => (v i : ℂ)))
  have hr' := neg_abs_le
    (quadratic (fun i => (v i : ℂ) + e i) - quadratic (fun i => (v i : ℂ))).re
  simp only [Complex.sub_re, quadratic_real] at hr hr'
  have hs0 := Real.sqrt_nonneg (absoluteEnergy e)
  have hs1 := Real.sqrt_nonneg q
  have hb : absoluteEnergy e ≤ eta ^ 2 * q := by
    nlinarith [mul_nonneg (sub_nonneg.mpr he) (add_nonneg hs0 (mul_nonneg heta hs1))]
  have hc : Real.sqrt q * Real.sqrt (absoluteEnergy e) ≤ eta * q := by
    nlinarith [mul_nonneg hs1 (sub_nonneg.mpr he)]
  change (1 - 2 * eta - eta ^ 2) * q ≤ _
  change ‖_‖ ≤ 2 * Real.sqrt q * Real.sqrt (absoluteEnergy e) + absoluteEnergy e at hp
  change |_ - q| ≤ _ at hr
  change -|_ - q| ≤ _ - q at hr'
  nlinarith

/-- The concrete positivity constant used in (4.43). -/
theorem quadratic_real_perturbation_pos {n : ℕ} (v : Fin n → ℝ) (e : Config n)
    (eta : ℝ) (heta : 0 ≤ eta) (heta' : eta ≤ 1 / 4)
    (hv : 0 < ∑ i, v i ^ 2)
    (he : Real.sqrt (absoluteEnergy e) ≤ eta * Real.sqrt (∑ i, v i ^ 2)) :
    0 < (quadratic (fun i => (v i : ℂ) + e i)).re := by
  have h := quadratic_real_perturbation_lower v e eta heta he
  have hc : 0 < 1 - 2 * eta - eta ^ 2 := by nlinarith [sq_nonneg (eta - 1/4)]
  exact lt_of_lt_of_le (mul_pos hc hv) h

theorem absoluteEnergy_scale {n : ℕ} (v : Config n) (c : ℂ) :
    absoluteEnergy (fun i => c * v i) = ‖c‖ ^ 2 * absoluteEnergy v := by
  simp [absoluteEnergy, mul_pow, Finset.mul_sum]

/-- Positivity on the full straight complex homotopy, rather than only on
its two endpoint cycles. The only metric premise is the near-identity bound. -/
theorem straight_homotopy_quadratic_pos {n : ℕ} (v : Fin n → ℝ) (e : Config n)
    (eta u : ℝ) (heta : 0 ≤ eta) (heta' : eta ≤ 1/4)
    (hu : 0 ≤ u) (hu' : u ≤ 1) (hv : 0 < ∑ i, v i ^ 2)
    (he : Real.sqrt (absoluteEnergy e) ≤ eta * Real.sqrt (∑ i, v i ^ 2)) :
    0 < (quadratic (fun i => (v i : ℂ) + (u : ℂ) * e i)).re := by
  apply quadratic_real_perturbation_pos v _ eta heta heta' hv
  apply le_trans _ he
  apply Real.sqrt_le_sqrt
  rw [absoluteEnergy_scale]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hq := absoluteEnergy_nonneg e
  nlinarith [mul_nonneg hq (show 0 ≤ 1 - u^2 by nlinarith)]

/-- The square-root denominator is bounded below uniformly, including on
all complex null cones. -/
theorem norm_rankOneCoefficient_le {n : ℕ} (ell : Config n) :
    ‖rankOneCoefficient ell‖ ≤ n := by
  have hp : 0 ≤ (Complex.sqrt (1 + (n : ℂ) * quadratic ell)).re := by
    change 0 ≤ ((1 + (n : ℂ) * quadratic ell) ^ (2⁻¹ : ℂ)).re
    rw [Complex.cpow_inv_two_re]
    positivity
  have hd : 1 ≤ ‖1 + Complex.sqrt (1 + (n : ℂ) * quadratic ell)‖ := by
    have hr := Complex.re_le_norm (1 + Complex.sqrt (1 + (n : ℂ) * quadratic ell))
    simp only [Complex.add_re, Complex.one_re] at hr
    linarith
  unfold rankOneCoefficient
  rw [norm_div]
  norm_cast
  exact div_le_self (Nat.cast_nonneg n) hd

/-- Exact Hermitian squared size of the rank-one displacement. -/
theorem meanCorrection_displacement_energy {n : ℕ} (ell w : Config n) :
    absoluteEnergy (fun i => meanCorrection ell w i - w i) =
      ‖rankOneCoefficient ell * pairing w ell‖ ^ 2 * absoluteEnergy ell := by
  simp only [meanCorrection, add_sub_cancel_left]
  exact absoluteEnergy_scale ell (rankOneCoefficient ell * pairing w ell)

/-- A dimension-explicit bound useful for uniform near-identity estimates.
The n-dependence is exactly polynomial, rather than an exponential dimension loss. -/
theorem meanCorrection_displacement_energy_le {n : ℕ} (ell w : Config n) :
    absoluteEnergy (fun i => meanCorrection ell w i - w i) ≤
      (n : ℝ)^2 * absoluteEnergy w * absoluteEnergy ell ^ 2 := by
  rw [meanCorrection_displacement_energy, norm_mul, mul_pow]
  have ha := norm_rankOneCoefficient_le ell
  have hp := norm_pairing_le w ell
  have he := absoluteEnergy_nonneg ell
  have hw := absoluteEnergy_nonneg w
  have hs1 := Real.sq_sqrt he
  have hs2 := Real.sq_sqrt hw
  have ha0 := norm_nonneg (rankOneCoefficient ell)
  have hp0 := norm_nonneg (pairing w ell)
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have haa : ‖rankOneCoefficient ell‖^2 ≤ (n : ℝ)^2 := by nlinarith
  have hpp : ‖pairing w ell‖^2 ≤ absoluteEnergy w * absoluteEnergy ell := by
    have hs := mul_nonneg (sub_nonneg.mpr hp)
      (add_nonneg hp0 (mul_nonneg (Real.sqrt_nonneg (absoluteEnergy w)) (Real.sqrt_nonneg (absoluteEnergy ell))))
    nlinarith
  calc
    _ ≤ (n : ℝ)^2 * (absoluteEnergy w * absoluteEnergy ell) * absoluteEnergy ell := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul haa hpp (sq_nonneg _) (sq_nonneg _)) he
    _ = _ := by ring

end
end IsingBulk.Anisotropic.NegativeNormalForm
