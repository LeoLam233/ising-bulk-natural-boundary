import IsingBulk.Anisotropic.NegativeDominance.GrowingLowSum
import IsingBulk.Anisotropic.NegativeDominance.CrossingOrderScale

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Filter
open scoped Topology

/-- The actual polynomial-radius Cauchy envelope is sub-main-scale uniformly
on the whole low range L≤log j. This is why radius N⁻³ suffices here. -/
theorem logarithmic_low_envelope_eventually {a D : ℝ} (ha : 0<a) (hD : 0<D) :
    ∀ᶠ j : ℕ in atTop, ∀ L : ℕ, (L : ℝ)≤Real.log j →
      D*(L : ℝ)^3*((L : ℝ)^3/a)^j ≤ Real.exp ((j : ℝ)*Real.log j/2) := by
  have ht : Tendsto (fun j : ℕ => Real.log (j : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ho := Real.isLittleO_log_id_atTop.comp_tendsto ht
  filter_upwards [ho.bound (by norm_num : (0 : ℝ)<1/24),
    ht.eventually (eventually_ge_atTop (max 1 (4*(|Real.log D|+|Real.log a|)))),
    eventually_ge_atTop (1 : ℕ)] with j hlo hlarge hj
  have hjR : (1 : ℝ)≤j := by exact_mod_cast hj
  have hlog : 1≤Real.log (j : ℝ) := (le_max_left _ _).trans hlarge
  have hconst : 4*(|Real.log D|+|Real.log a|)≤Real.log (j : ℝ) :=
    (le_max_right _ _).trans hlarge
  simp only [Function.comp_apply,id_eq,Real.norm_eq_abs] at hlo
  rw [abs_of_nonneg (by linarith : 0≤Real.log (j : ℝ))] at hlo
  have hsmall := (le_abs_self (Real.log (Real.log (j : ℝ)))).trans hlo
  intro L hL
  by_cases hz : L=0
  · subst L
    simp only [Nat.cast_zero,zero_pow (by norm_num : 3≠0),mul_zero,zero_mul]
    exact (Real.exp_pos _).le
  have hLpos : (0 : ℝ)<L := by exact_mod_cast (Nat.pos_of_ne_zero hz)
  have hLone : (1 : ℝ)≤L := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hz)
  have hlogL := Real.log_le_log hLpos hL
  have hlogL0 := Real.log_nonneg hLone
  apply (Real.log_le_iff_le_exp (by positivity : 0<D*(L : ℝ)^3*((L : ℝ)^3/a)^j)).mp
  rw [Real.log_mul (by positivity) (by positivity),Real.log_mul hD.ne' (by positivity),
    Real.log_pow,Real.log_pow,Real.log_div (by positivity) ha.ne',Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  have hc := le_abs_self (Real.log D)
  have hac := neg_abs_le (Real.log a)
  have hfirst : Real.log D+3*Real.log (L : ℝ)≤
      (j : ℝ)*(|Real.log D|+3*Real.log (L : ℝ)) := by
    nlinarith only [hc,mul_le_mul_of_nonneg_right hjR
      (show 0≤|Real.log D|+3*Real.log (L : ℝ) by positivity)]
  have hr : |Real.log D|+6*Real.log (L : ℝ)-Real.log a≤Real.log (j : ℝ)/2 := by
    linarith only [hlogL,hsmall,hconst,hac]
  have hm := mul_le_mul_of_nonneg_left hr (show (0 : ℝ)≤j by positivity)
  nlinarith only [hfirst,hm]

/-- Against the already proved main-model logarithmic growth rate, the whole
low envelope is exponentially negligible in the selected particle index. -/
theorem logarithmic_low_envelope_vs_growth {a D : ℝ} (ha : 0<a) (hD : 0<D) (K : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ j : ℕ, n≤j → j≤n^3 → ∀ L : ℕ,
      (L : ℝ)≤Real.log j → ∀ P : ℝ, 0<P →
      (j : ℝ)*(2*Real.log n-K)≤Real.log P →
      D*(L : ℝ)^3*((L : ℝ)^3/a)^j ≤ Real.exp (-(n : ℝ))*P := by
  obtain ⟨J,hJ⟩ := eventually_atTop.mp (logarithmic_low_envelope_eventually ha hD)
  have ht : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (max J 1),
    ht.eventually (eventually_ge_atTop (2*(K+1)))] with n hn hlogn
  intro j hnj hj L hL P hP hgrowth
  have hn1 : 1≤n := (le_max_right _ _).trans hn
  have hjJ : J≤j := ((le_max_left _ _).trans hn).trans hnj
  have hlogj := (crossing_order_log_bounds (j := (j : ℝ)) (by omega : 0<n)
    (by exact_mod_cast hnj) (by exact_mod_cast hj)).2
  have hrate : Real.log (j : ℝ)/2≤2*Real.log (n : ℝ)-K-1 := by linarith
  have hm := mul_le_mul_of_nonneg_left hrate (show (0 : ℝ)≤j by positivity)
  have hnjR : (n : ℝ)≤j := by exact_mod_cast hnj
  calc
    _ ≤ Real.exp ((j : ℝ)*Real.log j/2) := hJ j hjJ L hL
    _ ≤ Real.exp (-(n : ℝ)+Real.log P) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [hm,hgrowth,hnjR]
    _ = Real.exp (-(n : ℝ))*P := by rw [Real.exp_add,Real.exp_log hP]

end
end IsingBulk.Anisotropic.NegativeDominance
