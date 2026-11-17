import IsingBulk.AnisoF002.C03.IsotropicPeriodicDistance
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Exact fundamental-period integral of the oblique kernel majorant

The periodic distance is the actual quotient norm, and its reciprocal
regularization has the logarithmic integral required by F002 coarea.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology
open Set Metric MeasureTheory

def periodicKernel (p a x : ℝ) : ℝ := 1 / (a + periodicDistance p x)

theorem periodicKernel_nonneg (p a x : ℝ) (ha : 0 < a) : 0 ≤ periodicKernel p a x :=
  one_div_nonneg.mpr (add_nonneg ha.le (periodicDistance_nonneg p x))

theorem periodicKernel_continuous (p a : ℝ) (ha : 0 < a) : Continuous (periodicKernel p a) := by
  have hd : Continuous (periodicDistance p) := by
    unfold periodicDistance
    exact continuous_norm.comp continuous_quotient_mk'
  exact continuous_const.div (continuous_const.add hd)
    (fun x => (add_pos_of_pos_of_nonneg ha (periodicDistance_nonneg p x)).ne')

theorem periodicKernel_periodic (p a : ℝ) : Function.Periodic (periodicKernel p a) p := by
  intro x
  change 1 / (a + periodicDistance p (x + p)) = 1 / (a + periodicDistance p x)
  rw [periodicDistance_periodic p x]

theorem periodicKernel_neg (p a x : ℝ) : periodicKernel p a (-x) = periodicKernel p a x := by
  simp only [periodicKernel, periodicDistance, AddCircle.coe_neg, norm_neg]

theorem periodicDistance_fundamental (p x : ℝ) (hp : 0 < p) (hx : |x| ≤ p / 2) :
    periodicDistance p x = |x| := by
  apply (AddCircle.norm_coe_eq_abs_iff p hp.ne').mpr
  simpa only [abs_of_pos hp] using hx

theorem periodicKernel_positive_half_integral (p a : ℝ) (hp : 0 < p) (ha : 0 < a) :
    (∫ x in 0..p / 2, periodicKernel p a x) = Real.log (a + p / 2) - Real.log a := by
  have hp2 : 0 ≤ p / 2 := by positivity
  have he : (∫ x in 0..p / 2, periodicKernel p a x) = ∫ x in 0..p / 2, 1 / (a + x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hp2] at hx
    have hd := periodicDistance_fundamental p x hp (by rw [abs_of_nonneg hx.1]; exact hx.2)
    simp only [periodicKernel, hd, abs_of_nonneg hx.1]
  rw [he, intervalIntegral.integral_comp_add_left (fun x : ℝ => 1 / x) a, add_zero,
    integral_one_div_of_pos ha (by positivity), Real.log_div (by positivity) ha.ne']

theorem periodicKernel_fundamental_integral (p a : ℝ) (hp : 0 < p) (ha : 0 < a) :
    (∫ x in -(p / 2)..p / 2, periodicKernel p a x) =
      2 * (Real.log (a + p / 2) - Real.log a) := by
  have hcont := periodicKernel_continuous p a ha
  have hleft : (∫ x in -(p / 2)..0, periodicKernel p a x) = ∫ x in 0..p / 2, periodicKernel p a x := by
    have hh := intervalIntegral.integral_comp_neg (periodicKernel p a) (a := 0) (b := p / 2)
    simpa only [periodicKernel_neg, neg_zero] using hh.symm
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (-(p / 2)) 0) (hcont.intervalIntegrable 0 (p / 2)),
    hleft, periodicKernel_positive_half_integral p a hp ha]
  ring

/-- A positive periodic density costs at most one extra fundamental
period over an arbitrary interval. This applies to the exact periodic
kernel without making any regularity assumption at winding midpoints. -/
theorem nonnegative_periodic_interval_bound (f : ℝ → ℝ) (p : ℝ) (hp : 0 < p)
    (hf : Function.Periodic f p) (hcont : Continuous f) (hnonneg : ∀ x, 0 ≤ f x)
    (A B : ℝ) (hAB : A ≤ B) :
    (∫ x in A..B, f x) ≤ (1 + (B - A) / p) * (∫ x in 0..p, f x) := by
  let n : ℤ := ⌈(B - A) / p⌉
  have hnp : (B - A) / p ≤ (n : ℝ) := Int.le_ceil _
  have hupper : (n : ℝ) ≤ 1 + (B - A) / p := by
    have hh := (Int.ceil_lt_add_one ((B - A) / p)).le
    simpa only [n, add_comm] using hh
  have hendpoint : B ≤ A + (n : ℝ) * p := by
    have hh := (div_le_iff₀ hp).mp hnp
    linarith only [hh]
  have hmono := intervalIntegral.integral_mono_interval (μ := volume) (f := f) (a := A) (b := B) (c := A)
    (d := A + (n : ℝ) * p) le_rfl hAB hendpoint
    (Filter.Eventually.of_forall hnonneg) (hcont.intervalIntegrable _ _)
  have hperiod : (∫ x in A..A + (n : ℝ) * p, f x) = (n : ℝ) * (∫ x in 0..p, f x) := by
    have hh := hf.intervalIntegral_add_zsmul_eq n A (fun x y => hcont.intervalIntegrable x y)
    rw [hf.intervalIntegral_add_eq A 0, zero_add] at hh
    simpa only [zsmul_eq_mul] using hh
  rw [hperiod] at hmono
  exact hmono.trans (mul_le_mul_of_nonneg_right hupper
    (intervalIntegral.integral_nonneg_of_forall hp.le hnonneg))

/-- Uniform logarithmic cost on every finite interval, with a constant
depending only on the fixed winding period. -/
theorem exists_periodicKernel_log_integral_bound (p : ℝ) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, 0 < a → a ≤ 1 → ∀ A B : ℝ, A ≤ B →
      (∫ x in A..B, periodicKernel p a x) ≤
        C * (1 + (B - A)) * (1 + |Real.log a|) := by
  let K := 2 * (1 + |Real.log (1 + p / 2)|)
  let C := (1 + 1 / p) * K
  have hK : 0 < K := by dsimp [K]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro a ha ha1 A B hAB
  have hcont := periodicKernel_continuous p a ha
  have hper := periodicKernel_periodic p a
  have hperiod : (∫ x in 0..p, periodicKernel p a x) =
      2 * (Real.log (a + p / 2) - Real.log a) := by
    have hh := hper.intervalIntegral_add_eq 0 (-(p / 2))
    rw [zero_add, show -(p / 2) + p = p / 2 by ring,
      periodicKernel_fundamental_integral p a hp ha] at hh
    exact hh
  have hlog : Real.log (a + p / 2) ≤ Real.log (1 + p / 2) :=
    Real.log_le_log (by positivity) (by linarith only [ha1])
  have hJ : (∫ x in 0..p, periodicKernel p a x) ≤ K * (1 + |Real.log a|) := by
    rw [hperiod]
    have hla := neg_le_abs (Real.log a)
    have hlp := le_abs_self (Real.log (1 + p / 2))
    have hprod := mul_nonneg (abs_nonneg (Real.log (1 + p / 2))) (abs_nonneg (Real.log a))
    dsimp [K]
    nlinarith only [hlog, hla, hlp, hprod]
  have hcoeff : 1 + (B - A) / p ≤ (1 + 1 / p) * (1 + (B - A)) := by
    have hbp : 0 ≤ B - A := sub_nonneg.mpr hAB
    have hi : 0 ≤ 1 / p := by positivity
    have he : (B - A) / p = (B - A) * (1 / p) := by ring
    rw [he]
    nlinarith only [hbp, hi]
  have hbase := nonnegative_periodic_interval_bound (periodicKernel p a) p hp hper hcont
    (fun x => periodicKernel_nonneg p a x ha) A B hAB
  calc
    _ ≤ (1 + (B - A) / p) * (∫ x in 0..p, periodicKernel p a x) := hbase
    _ ≤ ((1 + 1 / p) * (1 + (B - A))) * (K * (1 + |Real.log a|)) :=
      mul_le_mul hcoeff hJ
        (intervalIntegral.integral_nonneg_of_forall hp.le (fun x => periodicKernel_nonneg p a x ha))
        (by positivity)
    _ = _ := by dsimp [C]; ring

end IsingBulk.AnisoF002.Isotropic
