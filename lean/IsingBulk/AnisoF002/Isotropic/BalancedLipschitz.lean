import IsingBulk.AnisoF002.Isotropic.VarianceCoercivity

/-!
# F002: uniform pair control of the actual balanced deformation

The population bounds are derived from the actual `N` bump values.
The displacement scale `τ/N` cancels that population bound, giving an
`N`-independent Lipschitz estimate and hence the actual contour's
coercive variance away from complete equality.
-/

namespace IsingBulk.AnisoF002.Isotropic

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Bumps taking values in `[0,1]` have populations between zero and `N`. -/
theorem bump_population_bounds (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) :
    0 ≤ (∑ i, p i) ∧ (∑ i, p i) ≤ (Fintype.card ι : ℝ) := by
  constructor
  · exact Finset.sum_nonneg fun i _ => (hp i).1
  · calc
      (∑ i, p i) ≤ ∑ _i : ι, (1 : ℝ) := Finset.sum_le_sum fun i _ => (hp i).2
      _ = (Fintype.card ι : ℝ) := by simp

/-- The exact `τ/N` scale removes the population factor from every pair difference. -/
theorem balancedShift_pair_lipschitz (θ p m : ι → ℝ) (τ Lp Lm : ℝ)
    (hn : 0 < Fintype.card ι) (hτ : 0 ≤ τ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (hm : ∀ i, 0 ≤ m i ∧ m i ≤ 1)
    (hpL : ∀ i j, |p i - p j| ≤ Lp * |θ i - θ j|)
    (hmL : ∀ i j, |m i - m j| ≤ Lm * |θ i - θ j|) (i j : ι) :
    |balancedShift (τ / Fintype.card ι) p m i -
      balancedShift (τ / Fintype.card ι) p m j| ≤
      (τ * (Lp + Lm)) * |θ i - θ j| := by
  have hP := bump_population_bounds p hp
  have hQ := bump_population_bounds m hm
  have hnR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hn
  have hs : 0 ≤ τ / (Fintype.card ι : ℝ) := div_nonneg hτ hnR.le
  rw [balancedShift_sub, abs_mul, abs_of_nonneg hs]
  have hb : |(∑ l, p l) * (m i - m j) - (∑ l, m l) * (p i - p j)| ≤
      (Fintype.card ι : ℝ) * ((Lp + Lm) * |θ i - θ j|) := by
    calc
      |(∑ l, p l) * (m i - m j) - (∑ l, m l) * (p i - p j)| ≤
          |(∑ l, p l) * (m i - m j)| + |(∑ l, m l) * (p i - p j)| :=
        abs_sub _ _
      _ = (∑ l, p l) * |m i - m j| + (∑ l, m l) * |p i - p j| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hP.1, abs_of_nonneg hQ.1]
      _ ≤ (Fintype.card ι : ℝ) * (Lm * |θ i - θ j|) +
          (Fintype.card ι : ℝ) * (Lp * |θ i - θ j|) := by
        exact add_le_add
          (mul_le_mul hP.2 (hmL i j) (abs_nonneg _) hnR.le)
          (mul_le_mul hQ.2 (hpL i j) (abs_nonneg _) hnR.le)
      _ = (Fintype.card ι : ℝ) * ((Lp + Lm) * |θ i - θ j|) := by ring
  calc
    τ / (Fintype.card ι : ℝ) *
        |(∑ l, p l) * (m i - m j) - (∑ l, m l) * (p i - p j)| ≤
        τ / (Fintype.card ι : ℝ) *
          ((Fintype.card ι : ℝ) * ((Lp + Lm) * |θ i - θ j|)) :=
      mul_le_mul_of_nonneg_left hb hs
    _ = (τ * (Lp + Lm)) * |θ i - θ j| := by
      field_simp

/-- Squared pair control for the complex bilinear variance. -/
theorem balancedShift_pair_sq_bound (θ p m : ι → ℝ) (τ Lp Lm : ℝ)
    (hn : 0 < Fintype.card ι) (hτ : 0 ≤ τ) (hLp : 0 ≤ Lp) (hLm : 0 ≤ Lm)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (hm : ∀ i, 0 ≤ m i ∧ m i ≤ 1)
    (hpL : ∀ i j, |p i - p j| ≤ Lp * |θ i - θ j|)
    (hmL : ∀ i j, |m i - m j| ≤ Lm * |θ i - θ j|) (i j : ι) :
    (balancedShift (τ / Fintype.card ι) p m i -
      balancedShift (τ / Fintype.card ι) p m j) ^ 2 ≤
      (τ * (Lp + Lm)) ^ 2 * (θ i - θ j) ^ 2 := by
  have hb := balancedShift_pair_lipschitz θ p m τ Lp Lm hn hτ hp hm hpL hmL i j
  have hs : |balancedShift (τ / Fintype.card ι) p m i -
      balancedShift (τ / Fintype.card ι) p m j| ^ 2 ≤
      ((τ * (Lp + Lm)) * |θ i - θ j|) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg _) (by positivity)).mpr hb
  simpa only [mul_pow, sq_abs] using hs

/-- The actual balanced contour has nonzero complex variance whenever it is not
at complete equality and the fixed deformation is sufficiently small. -/
theorem balancedContour_variance_ne_zero (θ p m : ι → ℝ) (τ Lp Lm : ℝ)
    (hn : 0 < Fintype.card ι) (hτ : 0 ≤ τ) (hLp : 0 ≤ Lp) (hLm : 0 ≤ Lm)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (hm : ∀ i, 0 ≤ m i ∧ m i ≤ 1)
    (hpL : ∀ i j, |p i - p j| ≤ Lp * |θ i - θ j|)
    (hmL : ∀ i j, |m i - m j| ≤ Lm * |θ i - θ j|)
    (hsmall : (τ * (Lp + Lm)) ^ 2 < 1)
    (i j : ι) (hij : θ i ≠ θ j) :
    pairVariance (contourCoordinate θ (balancedShift (τ / Fintype.card ι) p m)) ≠ 0 := by
  exact contour_variance_ne_zero θ _ (τ * (Lp + Lm)) hsmall
    (balancedShift_pair_sq_bound θ p m τ Lp Lm hn hτ hLp hLm hp hm hpL hmL) i j hij

end IsingBulk.AnisoF002.Isotropic
