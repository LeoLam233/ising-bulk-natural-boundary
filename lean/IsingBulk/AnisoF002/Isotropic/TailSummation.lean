import IsingBulk.AnisoF002.Isotropic.CellContraction

/-!
# F002: summation of the finite-cell Gaussian envelopes

The estimate here sums a genuine, explicitly specified Gaussian sequence,
with every fixed polynomial loss.  The complete physical differentiated
coefficients still need to be connected to this envelope by deformation,
transport and coarea; that analytic connection is not a premise smuggled
into a completed natural-boundary theorem.
-/
namespace IsingBulk.AnisoF002.Isotropic

open scoped BigOperators
open Filter

/-- A uniform elementary comparison with a geometric envelope. -/
theorem quadratic_exponent_bound (κ C x : ℝ) (hκ : 0 < κ) :
    -κ * x ^ 2 + C * x ≤ (C + κ / 2) ^ 2 / (4 * κ) - (κ / 2) * x := by
  have hid : -κ * x ^ 2 + C * x =
      ((C + κ / 2) ^ 2 / (4 * κ) - (κ / 2) * x) -
      (2 * κ * x - (C + κ / 2)) ^ 2 / (4 * κ) := by
    field_simp
    ring
  rw [hid]
  exact sub_le_self _ (div_nonneg (sq_nonneg _) (by positivity))

/-- Gaussian decay defeats every fixed polynomial loss uniformly over all N. -/
theorem summable_polynomial_gaussian (κ C : ℝ) (hκ : 0 < κ) (k : ℕ) :
    Summable (fun n : ℕ => (n : ℝ) ^ k * Real.exp (-κ * (n : ℝ) ^ 2 + C * n)) := by
  let D := (C + κ / 2) ^ 2 / (4 * κ)
  have hs := (Real.summable_pow_mul_exp_neg_nat_mul k (r := κ / 2) (by positivity)).mul_left
    (Real.exp D)
  apply hs.of_nonneg_of_le (fun n => by positivity)
  intro n
  have he := Real.exp_le_exp.mpr (quadratic_exponent_bound κ C (n : ℝ) hκ)
  calc
    (n : ℝ) ^ k * Real.exp (-κ * (n : ℝ) ^ 2 + C * n) ≤
        (n : ℝ) ^ k * Real.exp (D - (κ / 2) * n) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = Real.exp D * ((n : ℝ) ^ k * Real.exp (-(κ / 2) * n)) := by
      rw [sub_eq_add_neg, Real.exp_add, neg_mul]
      ring

/-- The factorial-normalized version used in F002 is summable too. -/
theorem summable_factorial_gaussian (κ C : ℝ) (hκ : 0 < κ) (k : ℕ) :
    Summable (fun n : ℕ => (n : ℝ) ^ k / n.factorial *
      Real.exp (-κ * (n : ℝ) ^ 2 + C * n)) := by
  apply (summable_polynomial_gaussian κ C hκ k).of_nonneg_of_le (fun n => by positivity)
  intro n
  have hf : (1 : ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_pos n
  exact mul_le_mul_of_nonneg_right (div_le_self (by positivity) hf) (Real.exp_nonneg _)

/-- A fixed retained collision block only changes the linear exponential loss. -/
theorem retained_block_exponent (κ C b ℓ n : ℝ) :
    -κ * (n - ℓ) ^ 2 + C * (n - ℓ) + b * ℓ * (n - ℓ) =
      -κ * n ^ 2 + (C + 2 * κ * ℓ + b * ℓ) * n -
        (κ * ℓ ^ 2 + C * ℓ + b * ℓ ^ 2) := by
  ring

/-- Every same-parity restriction is included by an ordinary summable subseries. -/
theorem summable_parity_gaussian (κ C : ℝ) (hκ : 0 < κ) (k q : ℕ) :
    Summable (fun n : ℕ => if n % 2 = q then (n : ℝ) ^ k *
      Real.exp (-κ * (n : ℝ) ^ 2 + C * n) else 0) := by
  apply (summable_polynomial_gaussian κ C hκ k).of_nonneg_of_le
  · intro n
    split_ifs <;> positivity
  · intro n
    split_ifs
    · exact le_rfl
    · positivity

/-- Summable control transfers to the actual coefficients once the separate
pointwise transport estimate has been proved. This is only that sum bridge. -/
theorem summable_of_gaussian_bound (f : ℕ → ℂ) (κ C A : ℝ)
    (hκ : 0 < κ) (k : ℕ)
    (hf : ∀ n, ‖f n‖ ≤ A * ((n : ℝ) ^ k *
      Real.exp (-κ * (n : ℝ) ^ 2 + C * n))) : Summable f := by
  exact Summable.of_norm_bounded ((summable_polynomial_gaussian κ C hκ k).mul_left A) hf

/-- A uniform finite-cell cover gives a summable family of complete pair products.
The local analytic construction of such cells for the physical factors remains separate. -/
theorem summable_complete_cell_products (K : ℕ) (hK : 0 < K)
    (c : ∀ n : ℕ, Fin n → Fin K) (P : ∀ n : ℕ, Fin n → Fin n → ℂ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hgap : (K : ℝ) * b < a + b)
    (hwithin : ∀ n i j, i < j → c n i = c n j → ‖P n i j‖ ≤ Real.exp (-a))
    (hall : ∀ n i j, i < j → ‖P n i j‖ ≤ Real.exp b) :
    Summable (fun n => ∏ ij ∈ indexPairs n, P n ij.1 ij.2) := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hκ : 0 < (a + b - (K : ℝ) * b) / (2 * K) :=
    div_pos (sub_pos.mpr hgap) (by positivity)
  apply summable_of_gaussian_bound _ ((a + b - (K : ℝ) * b) / (2 * K))
    (a / 2) 1 hκ 0
  intro n
  simpa only [pow_zero, one_mul, neg_div] using
    complete_pair_product_bound (c n) (P n) a b hK ha hb (hwithin n) (hall n)

end IsingBulk.AnisoF002.Isotropic
