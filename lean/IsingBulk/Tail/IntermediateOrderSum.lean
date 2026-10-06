import IsingBulk.Tail.SummationGrowth
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Finite intermediate-order summation of the displayed source budget.
The sector estimate itself is not supplied by this numerical lemma. -/
namespace IsingBulk.Tail
noncomputable section
open Filter Asymptotics
open scoped BigOperators Topology

def intermediateOrderBudget (C H : ℝ) (N : ℕ) : ℝ :=
  Real.exp (C*N*Real.log ((N:ℝ)+1))*(H+N)^C

theorem intermediate_order_budget_le {C D H : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hH : 1 ≤ H) (hDH : D^2 ≤ H) {N : ℕ} (hN : (N:ℝ) ≤ D*Real.sqrt H) :
    intermediateOrderBudget C H N ≤
      Real.exp (C*(D+2)*(Real.sqrt (H+2)*Real.log (H+2))) := by
  have hH0 : 0 ≤ H := by linarith
  have hs := Real.sq_sqrt hH0
  have hDroot : D ≤ Real.sqrt H := by nlinarith [Real.sqrt_nonneg H]
  have hNH : (N:ℝ) ≤ H := by nlinarith [Real.sqrt_nonneg H]
  have hroot : Real.sqrt H ≤ Real.sqrt (H+2) := Real.sqrt_le_sqrt (by linarith)
  have hroot1 : 1 ≤ Real.sqrt (H+2) := by
    have hh := Real.sq_sqrt (show 0 ≤ H+2 by linarith)
    nlinarith [Real.sqrt_nonneg (H+2)]
  have hlog : 0 ≤ Real.log (H+2) := Real.log_nonneg (by linarith)
  have hlogN : Real.log ((N:ℝ)+1) ≤ Real.log (H+2) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlogHN : Real.log (H+N) ≤ 2*Real.log (H+2) := by
    have ht := Real.log_le_log (show 0 < H+N by positivity)
      (show H+(N:ℝ) ≤ (H+2)^2 by nlinarith [(Nat.cast_nonneg N : (0:ℝ) ≤ N)])
    simpa only [Real.log_pow,Nat.cast_ofNat] using ht
  unfold intermediateOrderBudget
  rw [Real.rpow_def_of_pos (by positivity),← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hCN : C*(N:ℝ)*Real.log ((N:ℝ)+1) ≤ C*(N:ℝ)*Real.log (H+2) :=
    mul_le_mul_of_nonneg_left hlogN (by positivity)
  have hDN : C*(N:ℝ)*Real.log (H+2) ≤ C*D*Real.sqrt (H+2)*Real.log (H+2) := by
    have hn' := hN.trans (mul_le_mul_of_nonneg_left hroot hD)
    have hc' := mul_le_mul_of_nonneg_left hn' hC
    exact mul_le_mul_of_nonneg_right (by simpa only [mul_assoc] using hc') hlog
  have hCP := mul_le_mul_of_nonneg_right hlogHN hC
  have hR := mul_le_mul_of_nonneg_left hroot1 (mul_nonneg (show 0 ≤ 2*C by positivity) hlog)
  nlinarith

theorem intermediate_window_sum_bound {C D H : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hH : 1 ≤ H) (hDH : D^2 ≤ H) (S : Finset ℕ)
    (hS : ∀ N ∈ S, (N:ℝ) ≤ D*Real.sqrt H) :
    (∑ N ∈ S, intermediateOrderBudget C H N) ≤
      Real.exp ((C*(D+2)+1)*(Real.sqrt (H+2)*Real.log (H+2))) := by
  have hH0 : 0 ≤ H := by linarith
  have hs := Real.sq_sqrt hH0
  have hDroot : D ≤ Real.sqrt H := by nlinarith [Real.sqrt_nonneg H]
  have hNH (N : ℕ) (hN : N ∈ S) : (N:ℝ) ≤ H := by
    have ht := hS N hN
    nlinarith [Real.sqrt_nonneg H]
  have hsub : S ⊆ Finset.range (⌊H⌋₊+1) := by
    intro N hN
    apply Finset.mem_range.mpr
    have hh : N ≤ ⌊H⌋₊ := Nat.le_floor (hNH N hN)
    omega
  have hcard : (S.card:ℝ) ≤ H+2 := by
    have hh : S.card ≤ ⌊H⌋₊+1 := (Finset.card_le_card hsub).trans_eq (Finset.card_range _)
    have hr : (S.card:ℝ) ≤ (⌊H⌋₊:ℝ)+1 := by exact_mod_cast hh
    have hf := Nat.floor_le hH0
    linarith
  have hb := Finset.sum_le_sum (fun N hN => intermediate_order_budget_le hC hD hH hDH (hS N hN))
  simp only [Finset.sum_const, nsmul_eq_mul] at hb
  have hc := mul_le_mul_of_nonneg_right hcard
    (Real.exp_pos (C*(D+2)*(Real.sqrt (H+2)*Real.log (H+2)))).le
  apply hb.trans (hc.trans ?_)
  have hroot1 : 1 ≤ Real.sqrt (H+2) := by
    have hh := Real.sq_sqrt (show 0 ≤ H+2 by linarith)
    nlinarith [Real.sqrt_nonneg (H+2)]
  rw [show (H+2)*Real.exp (C*(D+2)*(Real.sqrt (H+2)*Real.log (H+2))) =
    Real.exp (Real.log (H+2)+C*(D+2)*(Real.sqrt (H+2)*Real.log (H+2))) by
      rw [Real.exp_add,Real.exp_log (by linarith : 0 < H+2)]]
  apply Real.exp_le_exp.mpr
  have hh := mul_le_mul_of_nonneg_right hroot1 (Real.log_nonneg (show 1 ≤ H+2 by linarith))
  nlinarith

theorem intermediate_window_sum_littleO {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (S : ℝ → Finset ℕ) (hS : ∀ H : ℝ, ∀ N ∈ S H, (N:ℝ) ≤ D*Real.sqrt H) :
    (fun H : ℝ => ∑ N ∈ S H, intermediateOrderBudget C H N) =o[atTop]
      (fun H : ℝ => Real.exp (H/2)) := by
  have hb : (fun H : ℝ => ∑ N ∈ S H, intermediateOrderBudget C H N) =O[atTop]
      (fun H : ℝ => Real.exp ((C*(D+2)+1)*(Real.sqrt (H+2)*Real.log (H+2)))) := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop (1:ℝ),eventually_ge_atTop (D^2)] with H hH hDH
    have hn : 0 ≤ ∑ N ∈ S H, intermediateOrderBudget C H N := by
      apply Finset.sum_nonneg
      intro N hN
      unfold intermediateOrderBudget
      positivity
    simpa only [Real.norm_eq_abs,abs_of_nonneg hn,abs_of_pos (Real.exp_pos _),one_mul] using
      intermediate_window_sum_bound hC hD hH hDH (S H) (hS H)
  exact hb.trans_isLittleO (by simpa only [mul_comm (Real.sqrt _) (Real.log _)] using
    intermediate_sum_growth_negligible (C*(D+2)+1))

end
end IsingBulk.Tail
