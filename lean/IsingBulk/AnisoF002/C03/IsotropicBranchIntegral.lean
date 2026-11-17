import IsingBulk.AnisoF002.C03.IsotropicBranchCoordinateBounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The actual inverse-square-root shell integral

The original real angular integral is estimated uniformly in its mean
and epsilon. The bound has exactly r/sqrt(|mu|+r+epsilon), including
intervals that cross the branch. No scale is differentiated.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology
open Set Metric MeasureTheory

def branchWeight (ε u : ℝ) : ℝ := 1 / Real.sqrt (|u| + ε)

theorem branchWeight_continuous {ε : ℝ} (hε : 0 < ε) : Continuous (branchWeight ε) := by
  apply continuous_const.div (Real.continuous_sqrt.comp (continuous_abs.add_const ε))
  intro u
  exact (Real.sqrt_pos.mpr (by linarith [abs_nonneg u])).ne'

theorem branchWeight_nonneg (ε u : ℝ) : 0 ≤ branchWeight ε u := by
  unfold branchWeight
  positivity

theorem branchWeight_integral_zero {ε R : ℝ} (hε : 0 < ε) (hR : 0 ≤ R) :
    (∫ u in 0..R, branchWeight ε u) = 2 * (Real.sqrt (R + ε) - Real.sqrt ε) := by
  have hd (u : ℝ) (hu : u ∈ uIcc 0 R) :
      HasDerivAt (fun x : ℝ => 2 * Real.sqrt (x + ε)) (branchWeight ε u) u := by
    rw [uIcc_of_le hR] at hu
    have hp : 0 < u + ε := by linarith [hu.1]
    have hh := (((hasDerivAt_id u).add_const ε).sqrt hp.ne').const_mul 2
    convert hh using 1
    · rfl
    · unfold branchWeight
      rw [abs_of_nonneg hu.1]
      simp only [id_eq]
      field_simp [(Real.sqrt_pos.mpr hp).ne']
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((branchWeight_continuous hε).intervalIntegrable 0 R)
  simpa only [zero_add, mul_sub] using hh

theorem branchWeight_integral_symmetric {ε R : ℝ} (hε : 0 < ε) (hR : 0 ≤ R) :
    (∫ u in -R..R, branchWeight ε u) = 4 * (Real.sqrt (R + ε) - Real.sqrt ε) := by
  have he : (∫ u in -R..0, branchWeight ε u) = ∫ u in 0..R, branchWeight ε u := by
    simpa only [neg_zero, branchWeight, abs_neg] using
      (intervalIntegral.integral_comp_neg (f := branchWeight ε) (a := 0) (b := R)).symm
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((branchWeight_continuous hε).intervalIntegrable (-R) 0)
    ((branchWeight_continuous hε).intervalIntegrable 0 R), he,
    branchWeight_integral_zero hε hR]
  ring

theorem branchWeight_integral_symmetric_rational {ε R : ℝ} (hε : 0 < ε) (hR : 0 ≤ R) :
    (∫ u in -R..R, branchWeight ε u) =
      4 * R / (Real.sqrt (R + ε) + Real.sqrt ε) := by
  rw [branchWeight_integral_symmetric hε hR]
  have hsum : 0 < Real.sqrt (R + ε) + Real.sqrt ε := by
    have h := Real.sqrt_pos.mpr hε
    linarith [Real.sqrt_nonneg (R + ε)]
  apply (eq_div_iff hsum.ne').mpr
  have h₁ := Real.sq_sqrt (by linarith : 0 ≤ R + ε)
  have h₂ := Real.sq_sqrt hε.le
  nlinarith only [h₁, h₂]

/-- Frozen F002's uniform branch interval envelope, with an explicit
absolute constant valid for every real mean and every positive scale. -/
theorem branchWeight_shell_integral_bound (μ r ε : ℝ) (hr : 0 < r) (hε : 0 < ε) :
    (∫ u in (μ - 2 * r)..(μ + 2 * r), branchWeight ε u) ≤
      24 * r / Real.sqrt (|μ| + r + ε) := by
  let T := |μ| + r + ε
  have hT : 0 < T := by dsimp [T]; positivity
  have hsT : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hint (a b : ℝ) : IntervalIntegrable (branchWeight ε) volume a b :=
    (branchWeight_continuous hε).intervalIntegrable a b
  have hab : μ - 2 * r ≤ μ + 2 * r := by linarith
  by_cases hμ : |μ| ≤ 4 * r
  · have hleft : -6 * r ≤ μ - 2 * r := by linarith [(abs_le.mp hμ).1]
    have hright : μ + 2 * r ≤ 6 * r := by linarith [(abs_le.mp hμ).2]
    have hm := intervalIntegral.integral_mono_interval hleft hab hright
      (Filter.Eventually.of_forall (fun u => branchWeight_nonneg ε u)) (hint (-6 * r) (6 * r))
    have hs : Real.sqrt T ≤ Real.sqrt (6 * r + ε) + Real.sqrt ε := by
      apply (Real.sqrt_le_sqrt (show T ≤ 6 * r + ε by dsimp [T]; linarith)).trans
      linarith [Real.sqrt_nonneg ε]
    calc
      _ ≤ ∫ u in -(6 * r)..(6 * r), branchWeight ε u := by simpa only [neg_mul] using hm
      _ = 24 * r / (Real.sqrt (6 * r + ε) + Real.sqrt ε) := by
        rw [branchWeight_integral_symmetric_rational hε (by positivity : 0 ≤ 6 * r)]
        ring
      _ ≤ 24 * r / Real.sqrt T := div_le_div_of_nonneg_left (by positivity) hsT hs
  · have hμlarge : 4 * r < |μ| := lt_of_not_ge hμ
    have hbound (u : ℝ) (hu : u ∈ Icc (μ - 2 * r) (μ + 2 * r)) :
        branchWeight ε u ≤ 2 / Real.sqrt T := by
      have hud : |μ - u| ≤ 2 * r := abs_le.mpr ⟨by linarith [hu.2], by linarith [hu.1]⟩
      have huabs : |μ| - 2 * r ≤ |u| := by
        have hh := abs_sub_abs_le_abs_sub μ u
        linarith
      have hscale : T ≤ 4 * (|u| + ε) := by dsimp [T]; linarith only [huabs, hμlarge, hε, hr]
      have hsF : 0 < Real.sqrt (|u| + ε) := Real.sqrt_pos.mpr (by linarith [abs_nonneg u])
      have hs : Real.sqrt T ≤ 2 * Real.sqrt (|u| + ε) := by
        apply Real.sqrt_le_iff.mpr
        refine ⟨by positivity, ?_⟩
        rw [mul_pow, Real.sq_sqrt (by linarith [abs_nonneg u])]
        norm_num
        exact hscale
      unfold branchWeight
      exact (div_le_div_iff₀ hsF hsT).mpr (by simpa only [one_mul] using hs)
    have hm := intervalIntegral.integral_mono_on hab (hint _ _)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => 2 / Real.sqrt T) volume
        (μ - 2 * r) (μ + 2 * r)) hbound
    have he : (∫ _u in (μ - 2 * r)..(μ + 2 * r), (2 / Real.sqrt T)) = 8 * r / Real.sqrt T := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring
    rw [he] at hm
    exact hm.trans (div_le_div_of_nonneg_right (by linarith) hsT.le)

end IsingBulk.AnisoF002.Isotropic
