import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
# F002: one retained degree and one dyadic scale for every higher order

These are the arithmetic and scale calculations in
`eq:iso-one-shell`.  They do not assert the preceding transport or
coarea estimate.  The radius inequality is valid on every positive
scale, including radii smaller than the inward distance.
-/

namespace IsingBulk.AnisoF002.Isotropic

/-- The exact first-singularity derivative budget. -/
def derivativeBudget (n : ℕ) : ℕ := (n * n - 1) / 2

/-- Retaining `n+1` variables gives this full squared-Vandermonde degree. -/
def retainedCollisionDegree (n : ℕ) : ℕ := (n + 1) * n

/-- The shell/flux degree has the claimed common lower bound at every higher order. -/
theorem retained_degree_lower (n N j : ℕ) (hn : 1 ≤ n)
    (hj : j ≤ derivativeBudget n) :
    (n : ℤ) + N - 2 ≤ (retainedCollisionDegree n : ℤ) + N - 3 - 2 * j := by
  have hsq : 1 ≤ n * n := by nlinarith
  have h2 : 2 * j ≤ n * n - 1 := by
    unfold derivativeBudget at hj
    omega
  have h2I : (2 : ℤ) * j ≤ (n : ℤ) * n - 1 := by
    exact_mod_cast h2
  simp only [retainedCollisionDegree, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  nlinarith

/-- The complete higher-particle range has strictly positive puncture/shell power. -/
theorem retained_degree_positive (n N j : ℕ) (hn : 1 ≤ n) (hN : n + 2 ≤ N)
    (hj : j ≤ derivativeBudget n) :
    0 < (retainedCollisionDegree n : ℤ) + N - 3 - 2 * j := by
  have hb := retained_degree_lower n N j hn hj
  have hnI : (1 : ℤ) ≤ n := by exact_mod_cast hn
  have hNI : (n : ℤ) + 2 ≤ N := by exact_mod_cast hN
  omega

/-- The square of F002's single mean scale, with `a = |mean| + ε`. -/
noncomputable def meanScaleSq (a r : ℝ) : ℝ := r ^ 2 / (a + r)

/-- Halving the radius contracts the squared scale by a factor between 1/4 and 1/2. -/
theorem meanScaleSq_half_bounds (a r : ℝ) (ha : 0 ≤ a) (hr : 0 < r) :
    (1 / 4 : ℝ) * meanScaleSq a r ≤ meanScaleSq a (r / 2) ∧
      meanScaleSq a (r / 2) ≤ (1 / 2 : ℝ) * meanScaleSq a r := by
  have hd : 0 < a + r := by linarith
  have hdh : 0 < a + r / 2 := by linarith
  unfold meanScaleSq
  constructor
  · rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hd hdh).2
    nlinarith [mul_nonneg ha (sq_nonneg r), mul_pos hr (sq_pos_of_pos hr)]
  · rw [← mul_div_assoc]
    apply (div_le_div_iff₀ hdh hd).2
    nlinarith [mul_nonneg ha (sq_nonneg r)]

/-- The physical scaled diameter. -/
noncomputable def meanScale (a r : ℝ) : ℝ := r / Real.sqrt (a + r)

theorem meanScale_sq (a r : ℝ) (ha : 0 ≤ a) (hr : 0 < r) :
    meanScale a r ^ 2 = meanScaleSq a r := by
  unfold meanScale meanScaleSq
  rw [div_pow, Real.sq_sqrt (by linarith)]

/-- The upper contraction used by the all-scale dyadic sum. -/
theorem meanScale_half_upper (a r : ℝ) (ha : 0 ≤ a) (hr : 0 < r) :
    meanScale a (r / 2) ≤ Real.sqrt (1 / 2 : ℝ) * meanScale a r := by
  have hs := (meanScaleSq_half_bounds a r ha hr).2
  have h1 := meanScale_sq a r ha hr
  have h2 := meanScale_sq a (r / 2) ha (by positivity)
  have hp : 0 ≤ meanScale a r := by unfold meanScale; positivity
  have hp2 : 0 ≤ meanScale a (r / 2) := by unfold meanScale; positivity
  apply (sq_le_sq₀ hp2 (mul_nonneg (Real.sqrt_nonneg _) hp)).1
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2), h1, h2]
  exact hs

/-- Its universal ratio is strictly below one. -/
theorem meanScale_ratio_lt_one : Real.sqrt (1 / 2 : ℝ) < 1 := by
  exact (Real.sqrt_lt' (by norm_num)).2 (by norm_num)

end IsingBulk.AnisoF002.Isotropic
