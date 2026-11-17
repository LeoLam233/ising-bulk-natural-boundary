import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# F002 negative HT: quantitative discrete peak estimates

This file proves the discrete mechanism used after the exact-factor estimates
in F002 §5.  It does not import any historical Ising theorem.  Its hypotheses
are explicit finite-difference inequalities; establishing those inequalities
for the exact physical model remains a separate obligation.
-/

namespace IsingBulk.AnisoF002.NegativeHT

open scoped BigOperators

/-- Strong concavity propagates the slope on every finite prefix. -/
theorem slope_bound_on_range (f : ℕ → ℝ) (c : ℝ) (K : ℕ)
    (hcurv : ∀ k, k + 2 ≤ K → f (k + 2) - 2 * f (k + 1) + f k ≤ -c)
    (k : ℕ) (hk : k + 1 ≤ K) :
    f (k + 1) - f k ≤ f 1 - f 0 - c * (k : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hk' : k + 1 ≤ K := by omega
      have hi := ih hk'
      have hc := hcurv k (by omega)
      push_cast
      nlinarith only [hi, hc]

/-- Summing the controlled slopes gives the exact quadratic cap. -/
theorem quadratic_cap_on_range (f : ℕ → ℝ) (c : ℝ) (K : ℕ)
    (hcurv : ∀ k, k + 2 ≤ K → f (k + 2) - 2 * f (k + 1) + f k ≤ -c)
    (k : ℕ) (hk : k ≤ K) :
    f k ≤ f 0 + (k : ℝ) * (f 1 - f 0) - c * (k : ℝ) * ((k : ℝ) - 1) / 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hi := ih (by omega)
      have hs := slope_bound_on_range f c K hcurv k (by omega)
      push_cast
      nlinarith only [hi, hs]

/-- A symmetric adjacent comparison converts centered curvature into two
strict gaps.  The error may have either sign. -/
theorem centered_adjacent_gaps {left center right c η : ℝ}
    (hcurv : right - 2 * center + left ≤ -c)
    (hcenter : |right - left| ≤ η) :
    left - center ≤ -(c - η) / 2 ∧
    right - center ≤ -(c - η) / 2 := by
  obtain ⟨hl, hr⟩ := abs_le.mp hcenter
  constructor <;> linarith

/-- The centered error is small enough to retain a Gaussian index penalty. -/
theorem gaussian_cap_on_range (f : ℕ → ℝ) (c : ℝ) (K : ℕ)
    (hc : 0 ≤ c)
    (hcurv : ∀ k, k + 2 ≤ K → f (k + 2) - 2 * f (k + 1) + f k ≤ -c)
    (hfirst : f 1 - f 0 ≤ -c / 4)
    (k : ℕ) (hk : k ≤ K) :
    f k - f 0 ≤ -(c / 4) * (k : ℝ)^2 := by
  have hcap := quadratic_cap_on_range f c K hcurv k hk
  have hm := mul_le_mul_of_nonneg_left hfirst (show (0 : ℝ) ≤ k by positivity)
  have hpoly : 0 ≤ (k : ℝ) * ((k : ℝ) - 1) := by
    by_cases hz : k = 0
    · subst k; norm_num
    · have h1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
      positivity
  have hp := mul_nonneg hc hpoly
  nlinarith only [hcap, hm, hp]

/-- Geometric prefix bound proved by its exact telescoping identity. -/
theorem geometric_tail_prefix_le {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (K : ℕ) :
    (∑ k ∈ Finset.range K, r ^ (k + 1)) ≤ r / (1 - r) := by
  have hid : (1-r) * (∑ k ∈ Finset.range K, r ^ (k+1)) = r - r ^ (K+1) := by
    induction K with
    | zero => simp
    | succ K ih =>
        rw [Finset.sum_range_succ]
        rw [mul_add, ih]
        simp only [pow_succ]
        ring
  apply (le_div_iff₀ (sub_pos.mpr hr1)).mpr
  have hp : 0 ≤ r ^ (K+1) := pow_nonneg hr _
  nlinarith only [hid, hp]

/-- A complete finite prefix of competitor moduli has a bound independent of
its length.  This is the whole-prefix estimate needed in the growing middle
window, rather than a pointwise nearest-neighbor assertion. -/
theorem exp_competitor_prefix_le (f : ℕ → ℝ) (c : ℝ) (K : ℕ)
    (hc : 0 < c)
    (hcurv : ∀ k, k + 2 ≤ K → f (k + 2) - 2 * f (k + 1) + f k ≤ -c)
    (hfirst : f 1 - f 0 ≤ -c / 4) :
    (∑ k ∈ Finset.range K, Real.exp (f (k+1) - f 0)) ≤
      Real.exp (-c/4) / (1 - Real.exp (-c/4)) := by
  have hr : 0 ≤ Real.exp (-c/4) := (Real.exp_pos _).le
  have hr1 : Real.exp (-c/4) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  apply le_trans (Finset.sum_le_sum (g := fun k => (Real.exp (-c/4))^(k+1)) ?_)
    (geometric_tail_prefix_le hr hr1 K)
  intro k hk
  have hkn : k+1 ≤ K := by have := Finset.mem_range.mp hk; omega
  have hg := gaussian_cap_on_range f c K hc.le hcurv hfirst (k+1) hkn
  have h1 : (1 : ℝ) ≤ (k+1 : ℕ) := by exact_mod_cast (show 1 ≤ k+1 by omega)
  have hpoly : ((k+1 : ℕ) : ℝ) ≤ ((k+1 : ℕ) : ℝ)^2 := by nlinarith
  have hexp : f (k+1) - f 0 ≤ (-c/4) * ((k+1 : ℕ) : ℝ) := by
    nlinarith [mul_nonneg hc.le (sub_nonneg.mpr hpoly)]
  calc
    Real.exp (f (k+1) - f 0) ≤ Real.exp ((-c/4) * ((k+1 : ℕ) : ℝ)) := Real.exp_le_exp.mpr hexp
    _ = (Real.exp (-c/4))^(k+1) := by rw [mul_comm, Real.exp_nat_mul]

/-- Two independently long sides of a centered discrete peak, with all
competitor moduli summed.  No phase relation is imposed. -/
theorem two_sided_competitor_bound (f g : ℕ → ℝ) (c η : ℝ) (K L : ℕ)
    (hc : 0 < c) (hη : η ≤ c/2) (hzero : g 0 = f 0)
    (hcenter : |f 1 - g 1| ≤ η)
    (hcentralCurv : f 1 - 2*f 0 + g 1 ≤ -c)
    (hf : ∀ k, k+2 ≤ K → f (k+2)-2*f (k+1)+f k ≤ -c)
    (hg : ∀ k, k+2 ≤ L → g (k+2)-2*g (k+1)+g k ≤ -c) :
    (∑ k ∈ Finset.range K, Real.exp (f (k+1)-f 0)) +
    (∑ k ∈ Finset.range L, Real.exp (g (k+1)-f 0)) ≤
      2 * (Real.exp (-c/4) / (1-Real.exp (-c/4))) := by
  obtain ⟨hleft, hright⟩ := centered_adjacent_gaps hcentralCurv hcenter
  have hfg : f 1-f 0 ≤ -c/4 := by linarith
  have hgg : g 1-g 0 ≤ -c/4 := by rw [hzero]; linarith
  have hf' := exp_competitor_prefix_le f c K hc hf hfg
  have hg' := exp_competitor_prefix_le g c L hc hg hgg
  rw [hzero] at hg'
  linarith

end IsingBulk.AnisoF002.NegativeHT
