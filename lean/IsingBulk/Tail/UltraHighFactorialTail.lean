import IsingBulk.Tail.ExteriorConvergenceBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! Uniform factorial tails at a quadratic logarithmic threshold. These scalar
bounds do not assume or replace the actual source form-factor estimate. -/
namespace IsingBulk.Tail
noncomputable section
open Filter Asymptotics
open scoped Topology

theorem factorial_term_geometric {B : ℝ} (hB : 0 ≤ B) {n : ℕ} (hn : 0 < n)
    (hscale : B*Real.exp 1 ≤ (n:ℝ)/2) :
    B^n/(n.factorial : ℝ) ≤ (1/2 : ℝ)^n := by
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  have htwo : 2*B ≤ (n:ℝ)/Real.exp 1 := by
    apply (le_div_iff₀ (Real.exp_pos 1)).mpr
    nlinarith
  have hp : (2*B)^n ≤ (n.factorial : ℝ) :=
    (pow_le_pow_left₀ (by positivity) htwo n).trans (factorial_lower_exp n)
  apply (div_le_iff₀ (by positivity : (0:ℝ)<n.factorial)).mpr
  have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ (1/2:ℝ)^n by positivity)
  have he : (1/2:ℝ)^n*(2*B)^n = B^n := by rw [← mul_pow]; congr 1; ring
  rw [he] at hm
  exact hm

theorem shifted_factorial_tail_bound {B : ℝ} (hB : 0 ≤ B) (K : ℕ) (hK : 0 < K)
    (hscale : B*Real.exp 1 ≤ (K:ℝ)/2) :
    (∑' m : ℕ, B^(K+m)/((K+m).factorial : ℝ)) ≤ 2*(1/2 : ℝ)^K := by
  have hs : Summable (fun m : ℕ => B^(K+m)/((K+m).factorial : ℝ)) :=
    (Real.summable_pow_div_factorial B).comp_injective (fun _ _ h => by omega)
  have hg : Summable (fun m : ℕ => (1/2:ℝ)^(K+m)) :=
    (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)).comp_injective
      (fun _ _ h => by omega)
  have hm : ∀ m : ℕ, B^(K+m)/((K+m).factorial : ℝ) ≤ (1/2:ℝ)^(K+m) := by
    intro m
    apply factorial_term_geometric hB (by omega)
    have hmR : (0:ℝ) ≤ m := Nat.cast_nonneg m
    push_cast
    linarith
  apply (hs.tsum_le_tsum hm hg).trans_eq
  simp_rw [pow_add]
  rw [tsum_mul_left,tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)]
  norm_num
  ring

def ultraHighFactorialThreshold (L H : ℝ) : ℕ := ⌈L*(H+1)^2⌉₊

def ultraHighFactorialTail (D L H : ℝ) : ℝ :=
  ∑' m : ℕ, (D*(H+1)^2)^(ultraHighFactorialThreshold L H+m)/
    ((ultraHighFactorialThreshold L H+m).factorial : ℝ)

theorem ultraHighFactorialTail_gaussian {D L H : ℝ} (hD : 0 ≤ D)
    (hL : 1 ≤ L) (hLD : 2*D*Real.exp 1 ≤ L) (hH : 0 ≤ H) :
    ultraHighFactorialTail D L H ≤ 2*Real.exp (-(Real.log 2)*L*(H+1)^2) := by
  have hceil : L*(H+1)^2 ≤ (ultraHighFactorialThreshold L H : ℝ) := Nat.le_ceil _
  have hK : 0 < ultraHighFactorialThreshold L H := by
    have hpos : (0:ℝ) < ultraHighFactorialThreshold L H := by nlinarith
    exact_mod_cast hpos
  have hscale : D*(H+1)^2*Real.exp 1 ≤ (ultraHighFactorialThreshold L H : ℝ)/2 := by
    have hh := mul_le_mul_of_nonneg_right hLD (sq_nonneg (H+1))
    nlinarith
  have ht := shifted_factorial_tail_bound (mul_nonneg hD (sq_nonneg _))
    (ultraHighFactorialThreshold L H) hK hscale
  apply ht.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
  have he : (1/2:ℝ)^(ultraHighFactorialThreshold L H) =
      Real.exp (-(Real.log 2)*(ultraHighFactorialThreshold L H : ℝ)) := by
    rw [mul_comm,Real.exp_nat_mul]
    congr 1
    rw [Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<2)]
    norm_num
  rw [he]
  apply Real.exp_le_exp.mpr
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

theorem gaussian_log_threshold_littleO (c A : ℝ) (hc : 0 < c) :
    (fun H : ℝ => Real.exp (-c*(H+1)^2)) =o[atTop]
      (fun H : ℝ => Real.exp (-A*H)) := by
  rw [Real.isLittleO_exp_comp_exp_comp]
  apply tendsto_atTop_mono' atTop _ tendsto_id
  filter_upwards [eventually_ge_atTop (0:ℝ),eventually_ge_atTop ((|A|+1)/c)] with H hH hlarge
  have hl : |A|+1 ≤ H*c := (div_le_iff₀ hc).mp hlarge
  have hm := mul_le_mul_of_nonneg_right hl hH
  have hA : A ≤ |A| := le_abs_self A
  have hAH := mul_le_mul_of_nonneg_right hA hH
  change H ≤ -A*H - -c*(H+1)^2
  nlinarith [mul_nonneg hc.le hH]

theorem ultraHighFactorialTail_littleO {D L : ℝ} (hD : 0 ≤ D)
    (hL : 1 ≤ L) (hLD : 2*D*Real.exp 1 ≤ L) (A : ℝ) :
    ultraHighFactorialTail D L =o[atTop] (fun H : ℝ => Real.exp (-A*H)) := by
  have hb : ultraHighFactorialTail D L =O[atTop]
      (fun H : ℝ => Real.exp (-(Real.log 2)*L*(H+1)^2)) := by
    apply IsBigO.of_bound 2
    filter_upwards [eventually_ge_atTop (0:ℝ)] with H hH
    have ht := ultraHighFactorialTail_gaussian hD hL hLD hH
    have hn : 0 ≤ ultraHighFactorialTail D L H := by
      apply tsum_nonneg
      intro m
      exact div_nonneg (pow_nonneg (mul_nonneg hD (sq_nonneg _)) _) (by positivity)
    simpa only [Real.norm_eq_abs,abs_of_nonneg hn,abs_of_pos (Real.exp_pos _)] using ht
  have hc : 0 < Real.log 2*L := mul_pos (Real.log_pos (by norm_num)) (by linarith)
  have hg := gaussian_log_threshold_littleO (Real.log 2*L) A hc
  exact hb.trans_isLittleO (by simpa only [neg_mul] using hg)

end
end IsingBulk.Tail
