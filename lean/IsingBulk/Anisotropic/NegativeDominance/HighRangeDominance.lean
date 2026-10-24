import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import IsingBulk.Anisotropic.NegativeDominance.HighRangeSummation
import IsingBulk.Anisotropic.NegativeDominance.UniformCrossingGrowth

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Filter
open scoped Topology
set_option maxHeartbeats 800000

/-- The complete high-range envelope is negligible against the proved main
model growth throughout the whole crossing interval, not just one witness. -/
theorem high_envelope_vs_growth (D K : ℝ) (hD : 0<D) :
    ∀ᶠ n : ℕ in atTop, ∀j : ℕ,n≤j →
      (j : ℝ)≤32*(n : ℝ)^2*Real.log n → ∀P : ℝ,0<P →
      (j : ℝ)*(2*Real.log n-K)≤Real.log P →
      D*Real.exp ((j : ℝ)*Real.log j-j*Real.sqrt (Real.log j)/32)≤Real.exp (-(n : ℝ))*P := by
  have ht : Tendsto (fun j : ℕ => Real.log (j : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hs := Real.tendsto_sqrt_atTop.comp ht
  have ho := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ)<1/2)).comp_tendsto ht
  have hev : ∀ᶠ j : ℕ in atTop,
      Real.log (Real.log (j : ℝ))+Real.log 32+K+2+|Real.log D|≤Real.sqrt (Real.log j)/32 := by
    filter_upwards [ho.bound (by norm_num : (0 : ℝ)<1/64),
      hs.eventually (eventually_ge_atTop (64*(|Real.log 32|+|K|+2+|Real.log D|)))] with j hlo hlarge
    simp only [Function.comp_apply,Real.norm_eq_abs] at hlo
    rw [←Real.sqrt_eq_rpow,abs_of_nonneg (Real.sqrt_nonneg _)] at hlo
    have hh := (le_abs_self (Real.log (Real.log (j : ℝ)))).trans hlo
    simp only [Function.comp_apply] at hlarge
    linarith only [hh,hlarge,le_abs_self (Real.log 32),le_abs_self K]
  obtain ⟨J,hJ⟩ := eventually_atTop.mp hev
  filter_upwards [eventually_ge_atTop (max J 2)] with n hn
  intro j hnj hj P hP hmain
  have hn2 : 2≤n := (le_max_right _ _).trans hn
  have hnR : (2 : ℝ)≤n := by exact_mod_cast hn2
  have hnjR : (n : ℝ)≤j := by exact_mod_cast hnj
  have hnp : (0 : ℝ)<n := by linarith
  have hjp : (0 : ℝ)<j := by linarith
  have hlognp : 0<Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hlogn := Real.log_le_log hnp hnjR
  have hloglog := Real.log_le_log hlognp hlogn
  have hlogj := Real.log_le_log hjp hj
  rw [Real.log_mul (by positivity) hlognp.ne',Real.log_mul (by norm_num) (by positivity),Real.log_pow] at hlogj
  norm_num only [Nat.cast_ofNat] at hlogj
  have hlarge := hJ j (((le_max_left _ _).trans hn).trans hnj)
  have hrate : Real.log (j : ℝ)-Real.sqrt (Real.log j)/32≤2*Real.log n-K-2-|Real.log D| := by
    linarith only [hlogj,hloglog,hlarge]
  have hm := mul_le_mul_of_nonneg_left hrate hjp.le
  have hc : Real.log D≤(j : ℝ)*|Real.log D| :=
    (le_abs_self _).trans (le_mul_of_one_le_left (abs_nonneg _) (by linarith))
  have hexp : Real.log D+((j : ℝ)*Real.log j-j*Real.sqrt (Real.log j)/32)≤-(n : ℝ)+Real.log P := by
    nlinarith only [hm,hc,hmain,hnjR,hnp.le]
  calc
    _ = Real.exp (Real.log D+((j : ℝ)*Real.log j-j*Real.sqrt (Real.log j)/32)) := by
      rw [Real.exp_add,Real.exp_log hD]
    _ ≤ Real.exp (-(n : ℝ)+Real.log P) := Real.exp_le_exp.mpr hexp
    _ = _ := by rw [Real.exp_add,Real.exp_log hP]


/-- The high envelope is negligible at every eligible crossing order, so it
uses exactly the integer selected for middle-index dominance. -/
theorem physical_high_on_crossing_range
    (B rootB : ℂ→ℂ) (phi : ℝ) (hB : AnalyticAt ℂ B 0) (hB0 : B 0≠0)
    (hroot : ContinuousAt rootB 0) (hroot0 : rootB 0≠0)
    (hsq : ∀ᶠ t in 𝓝 (0 : ℂ),rootB t^2=B t) (hphi : Real.sin phi≠0)
    (q : ℕ) (D : ℝ) (hD : 0<D) :
    ∃N : ℕ,∀n≥N,Odd n → ∀j : ℕ,
      lowerCrossingOrder n-1<(j : ℝ) → (j : ℝ)≤upperCrossingOrder n → n≤j →
      D*Real.exp ((j : ℝ)*Real.log j-j*Real.sqrt (Real.log j)/32)≤
        Real.exp (-(n : ℝ))*‖physicalModel B rootB phi (n+2*q) j‖ := by
  obtain ⟨K,Ng,hg⟩ := physical_growth_on_crossing_range B rootB phi hB hB0 hroot hroot0 hsq hphi q
  obtain ⟨Nh,hh⟩ := eventually_atTop.mp (high_envelope_vs_growth D K hD)
  obtain ⟨N,hN⟩ := eventually_atTop.mp
    (eventually_crossing_scale (|K|+1) (max Ng (max Nh 1)))
  refine ⟨N,?_⟩
  intro n hn ho j hjL hjH hnj
  obtain ⟨hnb,hlog,_hu⟩ := hN n hn
  have hnG : Ng≤n := (le_max_left _ _).trans hnb
  have hnH : Nh≤n := (le_max_left _ _).trans ((le_max_right _ _).trans hnb)
  have hn1 : 1≤n := (le_max_right _ _).trans ((le_max_right _ _).trans hnb)
  have hgrowth := hg n hnG ho j hjL hjH
  have hrate : 0<2*Real.log (n : ℝ)-K := by linarith [le_abs_self K,abs_nonneg K]
  have hjpos : (0 : ℝ)<j := by exact_mod_cast (show 0<j by omega)
  have hP : 0<‖physicalModel B rootB phi (n+2*q) j‖ := by
    by_contra h
    have he := le_antisymm (not_lt.mp h) (norm_nonneg _)
    rw [he,Real.log_zero] at hgrowth
    exact (not_le_of_gt (mul_pos hjpos hrate)) hgrowth
  exact hh n hnH j hnj hjH _ hP hgrowth

end
end IsingBulk.Anisotropic.NegativeDominance
