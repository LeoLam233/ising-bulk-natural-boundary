import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Tactic

/-!
# Fixed retained collision block in the F002 differentiated tail

For a first resonant particle number `n`, F002 retains `m = n + 1`
independent angles in every later same-parity coefficient.  This file checks
the entire derivative-order budget, the radial integrability criterion, and
the elementary uniform-in-epsilon majorant.  It does not assume or assert
that the actual numerator has been divided by its Vandermonde, or that the
actual kernel derivatives satisfy the required majorant.  Those analytic
connections remain separate obligations.
-/

namespace IsingBulk.AnisoF002.RegularTail
noncomputable section
open MeasureTheory Set

def oddTopOrder (n : ℕ) : ℕ := (n ^ 2 - 1) / 2
def evenTopOrder (n : ℕ) : ℕ := n ^ 2 / 2 - 1

theorem odd_derivative_budget {n j : ℕ} (hj : j ≤ oddTopOrder n) :
    2 * j ≤ n ^ 2 := by
  unfold oddTopOrder at hj
  omega

theorem even_derivative_budget {n j : ℕ} (hj : j ≤ evenTopOrder n) :
    2 * j ≤ n ^ 2 := by
  unfold evenTopOrder at hj
  omega

theorem retained_angles_independent {n N : ℕ} (hN : n + 2 ≤ N) :
    n + 1 ≤ N - 1 := by omega

theorem same_parity_later_independent (n r : ℕ) :
    n + 1 ≤ (n + 2 + 2 * r) - 1 := by omega

/-- The numerator degree after multiplying by the `m`-dimensional radial
Jacobian is `m²-1`; `m≥1` rules out truncated natural subtraction. -/
theorem radial_numerator_degree {m : ℕ} (hm : 1 ≤ m) :
    m * (m - 1) + (m - 1) = m * m - 1 := by
  have h1 : m * (m - 1) = m * m - m := by
    simpa using Nat.mul_sub_left_distrib m m 1
  have hmm : m ≤ m * m := by nlinarith
  omega

theorem fixed_block_degree_budget {n j : ℕ} (hn : 1 ≤ n) (hj : 2 * j ≤ n ^ 2) :
    2 * (j + 1) ≤ (n + 1) * (n + 1) - 1 := by
  have hsq : (n + 1) * (n + 1) = n ^ 2 + 2 * n + 1 := by ring
  omega

def radialExponent (n j : ℕ) : ℝ := ((n : ℝ) + 1) ^ 2 - 2 * (j : ℝ) - 3

theorem fixed_block_exponent_gt_neg_one {n j : ℕ}
    (hn : 1 ≤ n) (hj : 2 * j ≤ n ^ 2) :
    -1 < radialExponent n j := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hj' : 2 * (j : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hj
  unfold radialExponent
  nlinarith

theorem fixed_block_radial_integrable {n j : ℕ}
    (hn : 1 ≤ n) (hj : 2 * j ≤ n ^ 2) :
    IntegrableOn (fun r : ℝ => r ^ radialExponent n j) (Ioo 0 1) := by
  rw [intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1)]
  exact fixed_block_exponent_gt_neg_one hn hj

theorem odd_full_order_radial_integrable {n j : ℕ}
    (hn : 1 ≤ n) (hj : j ≤ oddTopOrder n) :
    IntegrableOn (fun r : ℝ => r ^ radialExponent n j) (Ioo 0 1) :=
  fixed_block_radial_integrable hn (odd_derivative_budget hj)

theorem even_full_order_radial_integrable {n j : ℕ}
    (hn : 1 ≤ n) (hj : j ≤ evenTopOrder n) :
    IntegrableOn (fun r : ℝ => r ^ radialExponent n j) (Ioo 0 1) :=
  fixed_block_radial_integrable hn (even_derivative_budget hj)

def radialKernel (m j : ℕ) (eps r : ℝ) : ℝ :=
  r ^ (m * m - 1) / (eps + r ^ 2) ^ (j + 1)

/-- Uniform majorant for every inward distance, including `eps=0`.
It is a bound on the explicit radial model, not on an unformalized integral. -/
theorem radial_kernel_le_power {m j : ℕ} {eps r : ℝ}
    (heps : 0 ≤ eps) (hr : 0 < r)
    (hbudget : 2 * (j + 1) ≤ m * m - 1) :
    radialKernel m j eps r ≤ r ^ (m * m - 1 - 2 * (j + 1)) := by
  have hdenpos : 0 < (r ^ 2) ^ (j + 1) := pow_pos (sq_pos_of_pos hr) _
  have hmono : (r ^ 2) ^ (j + 1) ≤ (eps + r ^ 2) ^ (j + 1) := by
    gcongr
    linarith
  unfold radialKernel
  calc
    r ^ (m * m - 1) / (eps + r ^ 2) ^ (j + 1) ≤
        r ^ (m * m - 1) / (r ^ 2) ^ (j + 1) :=
      div_le_div_of_nonneg_left (pow_nonneg hr.le _) hdenpos hmono
    _ = r ^ (m * m - 1 - 2 * (j + 1)) := by
      rw [← pow_mul, pow_sub₀ r hr.ne' hbudget, div_eq_mul_inv]

theorem fixed_block_uniform_majorant {n j : ℕ} {eps r : ℝ}
    (hn : 1 ≤ n) (hj : 2 * j ≤ n ^ 2) (heps : 0 ≤ eps) (hr : 0 < r) :
    radialKernel (n + 1) j eps r ≤
      r ^ ((n + 1) * (n + 1) - 1 - 2 * (j + 1)) :=
  radial_kernel_le_power heps hr (fixed_block_degree_budget hn hj)

end
end IsingBulk.AnisoF002.RegularTail
