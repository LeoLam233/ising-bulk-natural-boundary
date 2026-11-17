import IsingBulk.AnisoF002.NegativeHT.ExactFactors
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The actual first-winding pole-center scale

The scalar tau_n is exactly 1-cos(pi/n), as in F002. Positivity,
monotonicity, two-sided n^-2 bounds, and the exact normalized sinc identity
are proved here. This does not prove the moving-pole integral remainder.
-/

namespace IsingBulk.AnisoF002.NegativeHT

noncomputable section

open Filter
open scoped Topology

/-- The exact first-winding pole center. -/
def windingTau (n : ℕ) : ℝ := 1-Real.cos (Real.pi/(n:ℝ))

theorem windingTau_pos (n : ℕ) (hn : 0<n) : 0<windingTau n := by
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hn1 : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have ha : 0<Real.pi/(n:ℝ) := div_pos Real.pi_pos hn'
  have hb : Real.pi/(n:ℝ)≤Real.pi := by
    apply (div_le_iff₀ hn').mpr
    nlinarith [Real.pi_pos]
  have hc := Real.cos_lt_cos_of_nonneg_of_le_pi (show (0:ℝ)≤0 by rfl) hb ha
  simp only [Real.cos_zero] at hc
  exact sub_pos.mpr hc

/-- The pole centers decrease strictly with positive particle number. -/
theorem windingTau_strictAnti {l r : ℕ} (hl : 0<l) (hlr : l<r) :
    windingTau r < windingTau l := by
  have hl' : (0:ℝ)<l := by exact_mod_cast hl
  have hr' : (0:ℝ)<r := by exact_mod_cast (show 0<r by omega)
  have hn1 : (1:ℝ)≤l := by exact_mod_cast (show 1≤l by omega)
  have hb : Real.pi/(l:ℝ)≤Real.pi := by
    apply (div_le_iff₀ hl').mpr
    nlinarith [Real.pi_pos]
  have ha : Real.pi/(r:ℝ) < Real.pi/(l:ℝ) := by
    apply div_lt_div_of_pos_left Real.pi_pos hl'
    exact_mod_cast hlr
  have hc := Real.cos_lt_cos_of_nonneg_of_le_pi (div_nonneg Real.pi_pos.le hr'.le) hb ha
  unfold windingTau
  linarith

/-- Explicit elementary two-sided bounds at the actual first-winding center. -/
theorem windingTau_bounds (n : ℕ) (hn : 0<n) :
    2/(n:ℝ)^2 ≤ windingTau n ∧ windingTau n ≤ Real.pi^2/(2*(n:ℝ)^2) := by
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have hn1 : (1:ℝ)≤n := by exact_mod_cast (show 1≤n by omega)
  have hb : Real.pi/(n:ℝ)≤Real.pi := by
    apply (div_le_iff₀ hn').mpr
    nlinarith [Real.pi_pos]
  have hlow := Real.cos_le_one_sub_mul_cos_sq
    (x:=Real.pi/(n:ℝ)) (by rw [abs_of_nonneg (by positivity)]; exact hb)
  have hupp := Real.one_sub_sq_div_two_le_cos (x:=Real.pi/(n:ℝ))
  have hA : 2/Real.pi^2*(Real.pi/(n:ℝ))^2 = 2/(n:ℝ)^2 := by
    field_simp
  have hB : (Real.pi/(n:ℝ))^2/2 = Real.pi^2/(2*(n:ℝ)^2) := by ring
  unfold windingTau
  rw [hA] at hlow
  rw [hB] at hupp
  constructor <;> linarith

/-- Exact normalized representation. It exhibits the correction as an even
function of 1/n without replacing tau_n by its leading approximation. -/
theorem windingTau_normalized_sinc (n : ℕ) (hn : 0<n) :
    windingTau n * (n:ℝ)^2 / (Real.pi^2/2) =
      (Real.sinc (Real.pi/(2*(n:ℝ))))^2 := by
  have hn' : (n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hx : Real.pi/(2*(n:ℝ))≠0 := div_ne_zero Real.pi_ne_zero (mul_ne_zero (by norm_num) hn')
  rw [Real.sinc_of_ne_zero hx]
  have ht := Real.sin_sq_eq_half_sub (Real.pi/(2*(n:ℝ)))
  have he : 2*(Real.pi/(2*(n:ℝ))) = Real.pi/(n:ℝ) := by ring
  rw [he] at ht
  unfold windingTau
  rw [div_pow, ht]
  field_simp

/-- The exact pole-center normalization has the stated leading constant. -/
theorem tendsto_windingTau_scaled :
    Tendsto (fun n : ℕ => windingTau n*(n:ℝ)^2) atTop (𝓝 (Real.pi^2/2)) := by
  have ha : Tendsto (fun n : ℕ => Real.pi/(2*(n:ℝ))) atTop (𝓝 (0:ℝ)) := by
    convert tendsto_const_div_atTop_nhds_zero_nat (Real.pi/2) using 1
    ext n
    ring
  have hs : Tendsto (fun n : ℕ => Real.sinc (Real.pi/(2*(n:ℝ)))) atTop (𝓝 (1:ℝ)) := by
    simpa [Function.comp_def] using Real.continuous_sinc.continuousAt.tendsto.comp ha
  have ht : Tendsto (fun n : ℕ => (Real.pi^2/2)*(Real.sinc (Real.pi/(2*(n:ℝ))))^2)
      atTop (𝓝 (Real.pi^2/2)) := by
    simpa using (hs.pow 2).const_mul (Real.pi^2/2)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  have he := windingTau_normalized_sinc n hn
  have hA : Real.pi^2/2 ≠ 0 := by positivity
  have hx := (div_eq_iff hA).mp he
  simpa [mul_comm] using hx.symm

/-- The positive tau contribution to the exact integer-order comparison. -/
theorem log_windingTau_ratio_pos {l r : ℕ} (hl : 0<l) (hlr : l<r) :
    0 < Real.log (windingTau l/windingTau r) := by
  have hr : 0<r := by omega
  have hratio : 1<windingTau l/windingTau r := by
    exact (one_lt_div (windingTau_pos r hr)).mpr (windingTau_strictAnti hl hlr)
  exact Real.log_pos hratio

end

end IsingBulk.AnisoF002.NegativeHT
