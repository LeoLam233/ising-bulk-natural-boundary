import IsingBulk.Anisotropic.NegativeDominance.OddIndices
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Filter

def lowerCrossingOrder (n : ℕ) : ℝ := (n : ℝ)^2*Real.log n/16

def upperCrossingOrder (n : ℕ) : ℝ := 32*(n : ℝ)^2*Real.log n

theorem eventually_crossing_scale (L : ℝ) (N : ℕ) :
    ∀ᶠ n : ℕ in atTop, N ≤ n ∧ L ≤ Real.log (n : ℝ) ∧
      32*Real.log (n : ℝ) ≤ n := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog := (Real.tendsto_log_atTop.comp ht).eventually (eventually_ge_atTop L)
  have ho := Real.isLittleO_log_id_atTop.comp_tendsto ht
  filter_upwards [eventually_ge_atTop N, hlog, ho.bound (by norm_num : (0 : ℝ)<1/32)] with n hn hl he
  simp only [Function.comp_apply, id_eq, Real.norm_eq_abs] at he
  rw [abs_of_nonneg (show (0 : ℝ) ≤ n by positivity)] at he
  refine ⟨hn, hl, ?_⟩
  have hh := (le_abs_self (Real.log (n : ℝ))).trans he
  linarith

theorem crossing_order_range (n p : ℕ) (hn : 2 ≤ n) (hpn : 2*p ≤ n)
    (hodd : Odd n) (hl : 64 ≤ Real.log (n : ℝ)) (hu : 32*Real.log (n : ℝ) ≤ n) :
    2*(alpha (n+2*p) : ℝ) ≤ lowerCrossingOrder n-1 ∧
    (n : ℝ) ≤ lowerCrossingOrder n ∧
    lowerCrossingOrder n ≤ upperCrossingOrder n ∧
    upperCrossingOrder n ≤ (n : ℝ)^3 := by
  have ho : Odd (n+2*p) := by obtain ⟨k, rfl⟩ := hodd; exact ⟨k+p, by ring⟩
  have ha := two_mul_alpha_add_one (n+2*p) ho
  have har : 2*(alpha (n+2*p) : ℝ)+1=((n : ℝ)+2*p)^2 := by
    exact_mod_cast (ha.trans (pow_two (n+2*p)).symm)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 2*(p : ℝ) ≤ n := by exact_mod_cast hpn
  have hsq : ((n : ℝ)+2*p)^2 ≤ 4*(n : ℝ)^2 := by nlinarith
  have hlow := mul_le_mul_of_nonneg_left hl (sq_nonneg (n : ℝ))
  have hupp := mul_le_mul_of_nonneg_left hu (sq_nonneg (n : ℝ))
  dsimp [lowerCrossingOrder, upperCrossingOrder]
  constructor
  · nlinarith only [har, hsq, hlow]
  constructor
  · nlinarith only [hlow, hn2]
  constructor
  · nlinarith only [hlow, sq_nonneg (n : ℝ)]
  · nlinarith only [hupp]

theorem crossing_order_log_bounds {n : ℕ} {j : ℝ} (hn : 0 < n)
    (hlo : (n : ℝ) ≤ j) (hhi : j ≤ (n : ℝ)^3) :
    Real.log (n : ℝ) ≤ Real.log j ∧ Real.log j ≤ 3*Real.log (n : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨Real.log_le_log hn0 hlo, ?_⟩
  have h := Real.log_le_log (hn0.trans_le hlo) hhi
  simpa only [Real.log_pow, Nat.cast_ofNat] using h

end
end IsingBulk.Anisotropic.NegativeDominance
