import IsingBulk.Anisotropic.NegativeDominance.CrossingOrderScale
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Filter

/-- Every centered crossing witness places its selected particle strictly
above the low cutoff and inside the genuine full middle range. -/
theorem eventually_crossing_middle_range (q : ℕ) :
    ∀ᶠ n : ℕ in atTop,∀j : ℕ,
      lowerCrossingOrder n-1<(j : ℝ) → (j : ℝ)≤upperCrossingOrder n → n≤j →
      Real.log (j : ℝ)<((n+2*q : ℕ) : ℝ) ∧
      ((n+2*q : ℕ) : ℝ)^2≤(j : ℝ)/Real.sqrt (Real.log j) := by
  filter_upwards [eventually_crossing_scale 49152 (max 2 (2*q))] with n hn
  intro j hjL hjH hnj
  have hn2 : (2 : ℝ)≤n := by exact_mod_cast (le_max_left _ _).trans hn.1
  have hq : (2*q : ℝ)≤n := by exact_mod_cast (le_max_right _ _).trans hn.1
  have hnjR : (n : ℝ)≤j := by exact_mod_cast hnj
  have hjp : (0 : ℝ)<j := by linarith
  have hnp : (0 : ℝ)<n := by linarith
  have ht := hn.2.1
  have hu := hn.2.2
  have hjcube : (j : ℝ)≤(n : ℝ)^3 := by
    have hh := mul_le_mul_of_nonneg_left hu (sq_nonneg (n : ℝ))
    dsimp [upperCrossingOrder] at hjH
    nlinarith only [hh,hjH]
  have hlogj := Real.log_le_log hjp hjcube
  rw [Real.log_pow] at hlogj
  norm_num only [Nat.cast_ofNat] at hlogj
  have hlogjp : 0<Real.log (j : ℝ) := Real.log_pos (by linarith)
  have hSp : 0<Real.sqrt (Real.log j) := Real.sqrt_pos.mpr hlogjp
  have hss := Real.sq_sqrt hlogjp.le
  have hT2 := mul_le_mul_of_nonneg_right ht (show 0≤Real.log (n : ℝ) by linarith)
  have hS : Real.sqrt (Real.log j)≤Real.log n/128 := by
    nlinarith only [hss,hlogj,hT2,ht,Real.sqrt_nonneg (Real.log (j : ℝ))]
  have hbase : (n : ℝ)^2*Real.log n≤32*(j : ℝ) := by
    have hnq : (4 : ℝ)≤(n : ℝ)^2 := by nlinarith only [hn2]
    have hprod : 32≤(n : ℝ)^2*Real.log n := by nlinarith only [hnq,ht]
    dsimp [lowerCrossingOrder] at hjL
    linarith only [hprod,hjL]
  have hsize : ((n+2*q : ℕ) : ℝ)^2≤4*(n : ℝ)^2 := by
    push_cast
    nlinarith only [hq,hn2,Nat.cast_nonneg (α := ℝ) q]
  refine ⟨?_,(le_div_iff₀ hSp).mpr ?_⟩
  · push_cast
    nlinarith only [hlogj,hu,ht,Nat.cast_nonneg (α := ℝ) q]
  have hh := mul_le_mul hsize hS (Real.sqrt_nonneg _) (by positivity : 0≤4*(n : ℝ)^2)
  nlinarith only [hh,hbase]

end
end IsingBulk.Anisotropic.NegativeDominance
