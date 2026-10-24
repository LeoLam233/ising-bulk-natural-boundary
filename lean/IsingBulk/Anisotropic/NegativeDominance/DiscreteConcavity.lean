import Mathlib.Tactic

/-! The discrete summation step in ANISO §5.6. These lemmas are independent
of the analytic estimates: they turn actual second-difference bounds into
quadratic decay, without differentiating an asymptotic error. -/

namespace IsingBulk.Anisotropic.NegativeDominance

/-- A uniform second-difference bound controls every forward slope. -/
theorem slope_le_of_second_difference (f : ℕ → ℝ) (c : ℝ)
    (h : ∀ k, f (k + 2) - 2 * f (k + 1) + f k ≤ -c) :
    ∀ k, f (k + 1) - f k ≤ f 1 - f 0 - c * k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have hk := h k
      push_cast
      nlinarith

/-- Summing decreasing slopes gives the Gaussian-in-index exponent. -/
theorem quadratic_le_of_second_difference (f : ℕ → ℝ) (c : ℝ)
    (h : ∀ k, f (k + 2) - 2 * f (k + 1) + f k ≤ -c) :
    ∀ k, f k ≤ f 0 + k * (f 1 - f 0) - c * k * (k - 1 : ℝ) / 2 := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      have hs := slope_le_of_second_difference f c h k
      push_cast
      nlinarith

/-- Centered concavity and an approximately balanced adjacent pair give
both initial slope estimates; no phase or positivity of coefficients is used. -/
theorem adjacent_bounds_of_balance {a b z c e : ℝ}
    (hc : a - 2 * z + b ≤ -c) (hb : |a - b| ≤ e) :
    a - z ≤ (-c + e) / 2 ∧ b - z ≤ (-c + e) / 2 := by
  obtain ⟨hl, hu⟩ := abs_le.mp hb
  constructor <;> linarith

/-- Two-sided discrete Gaussian control on integer indices. In application
`f k = log ‖M(n + k*d,j_n)‖`; the hypotheses must be proved from the
exact factors, not supplied as a susceptibility interface. -/
theorem integer_quadratic_le_of_second_difference (f : ℤ → ℝ) (c e : ℝ)
    (h : ∀ k : ℤ, f (k + 1) - 2 * f k + f (k - 1) ≤ -c)
    (hb : |f 1 - f (-1)| ≤ e) (k : ℕ) :
    f (k : ℤ) ≤ f 0 - c * (k : ℝ)^2 / 2 + e * k / 2 ∧
    f (-(k : ℤ)) ≤ f 0 - c * (k : ℝ)^2 / 2 + e * k / 2 := by
  have ha := adjacent_bounds_of_balance (by simpa using h 0) hb
  have hp : ∀ m : ℕ,
      f ((m + 2 : ℕ) : ℤ) - 2 * f ((m + 1 : ℕ) : ℤ) + f (m : ℤ) ≤ -c := by
    intro m
    have h1 : (m : ℤ) + 1 + 1 = ((m + 2 : ℕ) : ℤ) := by omega
    have h2 : (m : ℤ) + 1 = ((m + 1 : ℕ) : ℤ) := by omega
    have h3 : (m : ℤ) + 1 - 1 = (m : ℤ) := by omega
    have hm := h ((m : ℤ) + 1)
    rw [h3, h1, h2] at hm
    exact hm
  have hn : ∀ m : ℕ,
      f (-((m + 2 : ℕ) : ℤ)) - 2 * f (-((m + 1 : ℕ) : ℤ)) +
        f (-(m : ℤ)) ≤ -c := by
    intro m
    have hm := h (-(m : ℤ) - 1)
    have h1 : -(m : ℤ) - 1 + 1 = -(m : ℤ) := by ring
    have h2 : -(m : ℤ) - 1 = -((m + 1 : ℕ) : ℤ) := by push_cast; ring
    have h3 : -(m : ℤ) - 1 - 1 = -((m + 2 : ℕ) : ℤ) := by push_cast; ring
    rw [h3, h1, h2] at hm
    linarith
  have qp := quadratic_le_of_second_difference (fun m => f (m : ℤ)) c hp k
  have qn := quadratic_le_of_second_difference (fun m => f (-(m : ℤ))) c hn k
  simp only [Nat.cast_zero, Nat.cast_one, neg_zero] at qp qn
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  constructor <;> nlinarith [mul_le_mul_of_nonneg_right ha.1 hk,
    mul_le_mul_of_nonneg_right ha.2 hk]

/-- Finite-window version of the slope bound. No concavity is required
outside the actual intermediate particle window. -/
theorem slope_le_on_range (f : ℕ → ℝ) (c : ℝ) (K : ℕ)
    (h : ∀ m, m < K → f (m + 2) - 2 * f (m + 1) + f m ≤ -c) :
    ∀ k, k ≤ K → f (k + 1) - f k ≤ f 1 - f 0 - c * k := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
      intro hk
      have hi := ih (by omega)
      have hs := h k (by omega)
      push_cast
      nlinarith

/-- Finite-window quadratic decay, retaining both endpoints. -/
theorem quadratic_le_on_range (f : ℕ → ℝ) (c : ℝ) (K : ℕ)
    (h : ∀ m, m < K → f (m + 2) - 2 * f (m + 1) + f m ≤ -c) :
    ∀ k, k ≤ K + 1 →
      f k ≤ f 0 + k * (f 1 - f 0) - c * k * (k - 1 : ℝ) / 2 := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
      intro hk
      have hi := ih (by omega)
      have hs := slope_le_on_range f c K h k (by omega)
      push_cast
      nlinarith

/-- A finite particle window with a controlled first slope gives the same
quadratic Gaussian exponent at every index of that window. -/
theorem quadratic_decay_on_range (f : ℕ → ℝ) (c e : ℝ) (K : ℕ)
    (h : ∀ m, m < K → f (m + 2) - 2 * f (m + 1) + f m ≤ -c)
    (hfirst : f 1 - f 0 ≤ (-c + e) / 2) (k : ℕ) (hk : k ≤ K + 1) :
    f k ≤ f 0 - c * (k : ℝ)^2 / 2 + e * k / 2 := by
  have hq := quadratic_le_on_range f c K h k hk
  have hm := mul_le_mul_of_nonneg_left hfirst (show (0 : ℝ) ≤ k by positivity)
  nlinarith

end IsingBulk.Anisotropic.NegativeDominance
