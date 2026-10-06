import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-! Scalar all-order summability of the actual microcore cubic decay budget. -/
namespace IsingBulk.Tail
noncomputable section
open Filter
open scoped Topology

theorem microcore_cubic_geometric_eventually (D a : ℝ) (ha : 0 < a) :
    ∀ᶠ N : ℕ in atTop,
      Real.exp (D*(N:ℝ)^2-a*(N:ℝ)*((N:ℝ)^2-1)) ≤ (Real.exp (-1))^N := by
  filter_upwards [eventually_ge_atTop (1:ℕ),
    eventually_ge_atTop ⌈(D+a+1)/a⌉₊] with N hN hcut
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hcutR : (⌈(D+a+1)/a⌉₊ : ℝ) ≤ N := by exact_mod_cast hcut
  have hratio : (D+a+1)/a ≤ (N:ℝ) := (Nat.le_ceil _).trans hcutR
  have hl : D+a+1 ≤ (N:ℝ)*a := (div_le_iff₀ ha).mp hratio
  have hm := mul_le_mul_of_nonneg_right hl (sq_nonneg (N:ℝ))
  have hNN : (N:ℝ) ≤ (N:ℝ)^2 := by nlinarith
  have hquad := mul_le_mul_of_nonneg_left hNN (show 0 ≤ a+1 by linarith)
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  nlinarith

theorem microcore_cubic_summable (D a : ℝ) (ha : 0 < a) :
    Summable (fun N : ℕ => Real.exp (D*(N:ℝ)^2-a*(N:ℝ)*((N:ℝ)^2-1))) := by
  have hs : Summable (fun N : ℕ => (Real.exp (-1))^N) :=
    summable_geometric_of_lt_one (Real.exp_nonneg _) (by rw [Real.exp_lt_one_iff]; norm_num)
  apply hs.of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [microcore_cubic_geometric_eventually D a ha] with N hN
  simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hN

theorem microcore_cubic_nat_exponent_summable (D a : ℝ) (ha : 0 < a) :
    Summable (fun N : ℕ => Real.exp (D*(N:ℝ)^2-a*(N:ℝ)*((N^2-1:ℕ):ℝ))) := by
  apply (microcore_cubic_summable D a ha).congr_cofinite
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop (1:ℕ)] with N hN
  have hn2 : 1 ≤ N^2 := by nlinarith
  simp only [Nat.cast_sub hn2,Nat.cast_pow,Nat.cast_one]

end
end IsingBulk.Tail
