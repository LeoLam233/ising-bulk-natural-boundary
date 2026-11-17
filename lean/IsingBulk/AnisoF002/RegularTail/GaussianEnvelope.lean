import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic

/-!
# Summability of the exact F002 numerator-envelope scale

The F002 matched-Pfaffian estimate has exponent `-κ N² + C N log(N+1)`.
This file derives summability for every fixed polynomial derivative loss.
The estimate on the physical numerator, its parameter derivatives, and the
integrated kernel must still be established separately.  No old tail theorem
is imported, and no assumption of a full tail conclusion is concealed here.
-/

namespace IsingBulk.AnisoF002.RegularTail
open Filter

theorem eventually_log_absorption {kappa C : ℝ} (hk : 0 < kappa) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop,
      C * (n : ℝ) * Real.log ((n : ℝ) + 1) ≤ kappa / 2 * (n : ℝ) ^ 2 := by
  let e : ℝ := kappa / (4 * (C + 1))
  have he : 0 < e := by dsimp [e]; positivity
  have heq : 4 * (C + 1) * e = kappa := by
    dsimp [e]
    field_simp
  have hcoefficient : 2 * C * e ≤ kappa / 2 := by nlinarith
  have htend : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hlog := htend.eventually (Real.isLittleO_log_id_atTop.bound he)
  filter_upwards [hlog, eventually_ge_atTop (1 : ℕ)] with n hl hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have harg : 0 ≤ (n : ℝ) + 1 := by positivity
  simp only [Real.norm_eq_abs, id_eq, abs_of_nonneg harg] at hl
  have hlog' : Real.log ((n : ℝ) + 1) ≤ e * ((n : ℝ) + 1) :=
    (le_abs_self _).trans hl
  calc
    C * (n : ℝ) * Real.log ((n : ℝ) + 1) ≤ C * n * (e * (n + 1)) := by
      exact mul_le_mul_of_nonneg_left hlog' (by positivity)
    _ ≤ (2 * C * e) * (n : ℝ) ^ 2 := by
      have hh := mul_le_mul_of_nonneg_left (show (n : ℝ) + 1 ≤ 2 * n by linarith)
        (show 0 ≤ C * (n : ℝ) * e by positivity)
      nlinarith
    _ ≤ kappa / 2 * (n : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hcoefficient (sq_nonneg _)

theorem eventually_gaussian_exponent_le_linear {kappa C : ℝ}
    (hk : 0 < kappa) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop,
      -kappa * (n : ℝ) ^ 2 + C * n * Real.log ((n : ℝ) + 1) ≤
        -(kappa / 2) * (n : ℝ) := by
  filter_upwards [eventually_log_absorption hk hC, eventually_ge_atTop (1 : ℕ)] with n hb hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hsq (show 0 ≤ kappa / 2 by positivity)
  linarith

theorem gaussian_log_envelope_summable (j : ℕ) {kappa C : ℝ}
    (hk : 0 < kappa) (hC : 0 ≤ C) :
    Summable (fun n : ℕ => (n : ℝ) ^ j *
      Real.exp (-kappa * (n : ℝ) ^ 2 + C * n * Real.log ((n : ℝ) + 1))) := by
  apply (Real.summable_pow_mul_exp_neg_nat_mul j (half_pos hk)).of_norm_bounded_eventually_nat
  filter_upwards [eventually_gaussian_exponent_le_linear hk hC] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hn) (by positivity)

/-- Arbitrary complex phases are permitted.  The only premise on `a` is
the explicit eventual envelope, not summability or noncancellation. -/
theorem summable_of_gaussian_log_envelope {a : ℕ → ℂ} (j : ℕ)
    {kappa C K : ℝ} (hk : 0 < kappa) (hC : 0 ≤ C)
    (hbound : ∀ᶠ n : ℕ in atTop, ‖a n‖ ≤ K * ((n : ℝ) ^ j *
      Real.exp (-kappa * (n : ℝ) ^ 2 + C * n * Real.log ((n : ℝ) + 1)))) :
    Summable a :=
  ((gaussian_log_envelope_summable j hk hC).mul_left K).of_norm_bounded_eventually_nat hbound

end IsingBulk.AnisoF002.RegularTail
