import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! Uniform (not pointwise-in-N) intermediate-window estimates. Fixed
constants and the threshold precede all particle orders in N≤D√H. -/
namespace IsingBulk.Tail
noncomputable section
open Filter
open scoped Topology

theorem linear_sqrt_absorbed (H D C r n : ℝ)
    (hH : 0 ≤ H) (hD : 0 ≤ D) (hC : 0 ≤ C) (hr : 0 < r)
    (hn : n ≤ D*Real.sqrt H) (hlarge : (2*C*D/r)^2 ≤ H) :
    C*n ≤ r*H/2 := by
  have hsq : (Real.sqrt H)^2=H := Real.sq_sqrt hH
  have hsqrt : 0 ≤ Real.sqrt H := Real.sqrt_nonneg H
  have hb : 2*C*D/r ≤ Real.sqrt H := by
    have hnon : 0 ≤ 2*C*D/r := by positivity
    nlinarith
  have hb' := (div_le_iff₀ hr).mp hb
  have hp := mul_le_mul_of_nonneg_right hb' hsqrt
  have hn' := mul_le_mul_of_nonneg_left hn hC
  nlinarith

theorem polynomial_le_exp (n : ℝ) (hn : 0 ≤ n) (m : ℕ) :
    n^m ≤ Real.exp ((m:ℝ)*n) := by
  have he : n ≤ Real.exp n := by linarith [Real.add_one_le_exp n]
  calc
    n^m ≤ (Real.exp n)^m := pow_le_pow_left₀ hn he m
    _ = _ := by rw [← Real.exp_nat_mul]

/-- One explicit threshold works simultaneously for every N in the window.
The remaining exp(-rH/2) bound tends to zero. -/
theorem intermediate_window_decay_bound (D C r : ℝ) (m : ℕ)
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hr : 0 < r) :
    ∀ᶠ H : ℝ in atTop, ∀ N : ℕ, (N:ℝ) ≤ D*Real.sqrt H →
      Real.exp (-r*H)*Real.exp (C*N)*(N:ℝ)^m ≤ Real.exp (-r*H/2) := by
  filter_upwards [eventually_ge_atTop (max 0 ((2*(C+(m:ℝ))*D/r)^2))] with H hH
  have hH0 : 0 ≤ H := (le_max_left _ _).trans hH
  have hHsq : (2*(C+(m:ℝ))*D/r)^2 ≤ H := (le_max_right _ _).trans hH
  intro N hN
  have hn : 0 ≤ (N:ℝ) := Nat.cast_nonneg _
  have hlin := linear_sqrt_absorbed H D (C+(m:ℝ)) r N hH0 hD (by positivity) hr hN hHsq
  calc
    _ ≤ Real.exp (-r*H)*Real.exp (C*N)*Real.exp ((m:ℝ)*N) := by
      gcongr
      exact polynomial_le_exp N hn m
    _ = Real.exp (-r*H+(C+(m:ℝ))*N) := by rw [← Real.exp_add,← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

/-- Uniform epsilon-smallness, expressed with ε=exp(-H), for every fixed
polynomial and exponential loss. The threshold is outside the N quantifier. -/
theorem intermediate_window_uniform_small (D C r : ℝ) (m : ℕ)
    (hD : 0 ≤ D) (hC : 0 ≤ C) (hr : 0 < r) (b : ℝ) (hb : 0 < b) :
    ∀ᶠ H : ℝ in atTop, ∀ N : ℕ, (N:ℝ) ≤ D*Real.sqrt H →
      Real.exp (-r*H)*Real.exp (C*N)*(N:ℝ)^m < b := by
  have ht : Tendsto (fun H : ℝ => Real.exp (-r*H/2)) atTop (𝓝 0) := by
    have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (show 0 < r/2 by positivity))
    convert hh using 1
    ext H
    congr 1
    simp only [id_eq]
    ring
  filter_upwards [intermediate_window_decay_bound D C r m hD hC hr,
    ht.eventually (gt_mem_nhds hb)] with H hH hsmall
  intro N hN
  exact (hH N hN).trans_lt hsmall

end
end IsingBulk.Tail
