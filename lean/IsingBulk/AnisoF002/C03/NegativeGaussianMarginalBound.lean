import IsingBulk.AnisoF002.C03.NegativeGaussianMarginalCoordinates
import Mathlib.Analysis.MeanInequalities

/-!
# The complete marginal insertion-product estimate

The full product of the new coordinate's squared differences is bounded
using the zero-sum AM--GM identity.  Every needed radial moment is an
actual proved Gaussian expectation.  Binomial integration then yields
the dimension-dependent polynomial bound used to obtain the uniform
angular exponential moment.
-/

namespace IsingBulk.AnisoF002.NegativeHT.Angular
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal

theorem nonnegative_prod_le_mean_pow {m : ℕ} (hm : 0 < m)
    (f : Fin m → ℝ) (hf : ∀ i, 0 ≤ f i) :
    (∏ i, f i) ≤ ((∑ i, f i) / (m : ℝ)) ^ m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hp : 0 ≤ ∏ i, f i := Finset.prod_nonneg (fun i _ => hf i)
  have h := Real.geom_mean_le_arith_mean Finset.univ (fun _ : Fin m => (1 : ℝ)) f
    (by intro i _; norm_num) (by simpa using hmR) (by intro i _; exact hf i)
  simp only [Real.rpow_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, one_mul] at h
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg hp _) h m
  rw [← Real.rpow_mul_natCast hp, inv_mul_cancel₀ hmR.ne', Real.rpow_one] at hpow
  exact hpow

theorem marginal_insertion_amgm {d : ℕ} (u : constrainedPlane d) (a : ℝ) :
    (∏ i, (a - (u : Ambient d) i) ^ 2) ≤
      (a ^ 2 + ‖u‖ ^ 2 / ((d + 1 : ℕ) : ℝ)) ^ (d + 1) := by
  have h := nonnegative_prod_le_mean_pow (Nat.succ_pos d)
    (fun i => (a - (u : Ambient d) i) ^ 2) (fun i => sq_nonneg _)
  have hs : (∑ i, (a - (u : Ambient d) i) ^ 2) =
      ((d + 1 : ℕ) : ℝ) * a ^ 2 + ‖u‖ ^ 2 := by
    rw [constrained_norm_sq]
    simp_rw [sub_sq]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp only [← Finset.mul_sum, constrained_sum, mul_zero, sub_zero,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hs, add_div, mul_div_cancel_left₀ _ (by positivity)] at h
  exact h

theorem gaussianLaw_scaled_quadratic_integrable {d : ℕ} (hd : 0 < d) (k : ℕ) :
    Integrable (fun v : constrainedPlane d =>
      (‖v‖ ^ 2 / ((d + 1 : ℕ) : ℝ)) ^ k) (gaussianLaw d) := by
  simpa only [div_pow] using
    (gaussianLaw_quadratic_moment_integrable hd k).div_const (((d + 1 : ℕ) : ℝ) ^ k)

theorem gaussianLaw_shifted_quadratic_integrable {d : ℕ} (hd : 0 < d) (a : ℝ) (k : ℕ) :
    Integrable (fun v : constrainedPlane d =>
      (a + ‖v‖ ^ 2 / ((d + 1 : ℕ) : ℝ)) ^ k) (gaussianLaw d) := by
  simp_rw [add_pow]
  apply integrable_finsetSum
  intro j _
  exact ((gaussianLaw_scaled_quadratic_integrable hd (k - j)).const_mul (a ^ j)).mul_const _

theorem gaussianLaw_shifted_quadratic_integral_le {d : ℕ} (hd : 0 < d)
    {a : ℝ} (ha : 0 ≤ a) :
    (∫ v : constrainedPlane d,
      (a + ‖v‖ ^ 2 / ((d + 1 : ℕ) : ℝ)) ^ (d + 1) ∂gaussianLaw d) ≤
      (a + ((d + 2 : ℕ) : ℝ)) ^ (d + 1) := by
  simp_rw [add_pow]
  rw [integral_finsetSum]
  · apply Finset.sum_le_sum
    intro j _
    rw [integral_mul_const, integral_const_mul]
    apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg ha _)
    exact gaussianLaw_scaled_quadratic_moment_le hd (Nat.sub_le _ _)
  · intro j _
    exact ((gaussianLaw_scaled_quadratic_integrable hd (d + 1 - j)).const_mul (a ^ j)).mul_const _

theorem marginalScale_sq_le_three {d : ℕ} (hd : 0 < d) :
    marginalScale d ^ 2 ≤ 3 := by
  have hc : marginalScale d ≤ 3 / 2 := by
    rw [marginalScale, div_le_iff₀ (by positivity)]
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
    push_cast
    linarith
  nlinarith [marginalScale_pos d]

theorem marginal_insertion_le_polynomial {d : ℕ} (hd : 0 < d)
    (u : constrainedPlane d) (x : ℝ) :
    (∏ i, (marginalScale d * x - (u : Ambient d) i) ^ 2) ≤
      (3 * x ^ 2 + ‖u‖ ^ 2 / ((d + 1 : ℕ) : ℝ)) ^ (d + 1) := by
  apply (marginal_insertion_amgm u (marginalScale d * x)).trans
  apply pow_le_pow_left₀ (by positivity)
  rw [mul_pow]
  gcongr
  exact marginalScale_sq_le_three hd

theorem marginal_insertion_integrable {d : ℕ} (hd : 0 < d) (x : ℝ) :
    Integrable (fun u : constrainedPlane d =>
      ∏ i, (marginalScale d * x - (u : Ambient d) i) ^ 2) (gaussianLaw d) := by
  apply (gaussianLaw_shifted_quadratic_integrable hd (3 * x ^ 2) (d + 1)).mono'
    (by fun_prop)
  apply Filter.Eventually.of_forall
  intro u
  rw [Real.norm_of_nonneg (Finset.prod_nonneg (fun _ _ => sq_nonneg _))]
  exact marginal_insertion_le_polynomial hd u x

/-- Exactly the full insertion-product bound in the frozen one-coordinate marginal proof. -/
theorem marginal_insertion_expectation_le {d : ℕ} (hd : 0 < d) (x : ℝ) :
    (∫ u : constrainedPlane d,
      ∏ i, (marginalScale d * x - (u : Ambient d) i) ^ 2 ∂gaussianLaw d) ≤
      (3 * x ^ 2 + ((d + 2 : ℕ) : ℝ)) ^ (d + 1) := by
  apply (integral_mono (marginal_insertion_integrable hd x)
    (gaussianLaw_shifted_quadratic_integrable hd (3 * x ^ 2) (d + 1))
    (fun u => marginal_insertion_le_polynomial hd u x)).trans
  exact gaussianLaw_shifted_quadratic_integral_le hd (by positivity)

end
end IsingBulk.AnisoF002.NegativeHT.Angular
