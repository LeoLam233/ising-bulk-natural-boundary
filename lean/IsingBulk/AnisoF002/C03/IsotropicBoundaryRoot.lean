import IsingBulk.AnisoF002.C03.IsotropicDeformationSheet
import IsingBulk.AnisoF002.Isotropic.ExplicitRightInverse

/-!
# The full physical upper boundary root, including the branch endpoint

The boundary root is given by real square roots, so its boundary value is
continuous across W=1 and on the left arc. A division-free quadratic
identity gives a uniform Holder estimate for the actual interior root.
This supplies the square-root continuity needed for actual deformed-image
inclusion, without selecting unrelated local inverses.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology
open Filter Set Metric
open IsingBulk.AnisoF002.RegularTail

def upperBoundaryRoot (x : ℝ) : ℂ :=
  (x : ℂ) - (Real.sqrt (x ^ 2 - 1) : ℂ) - Complex.I * (Real.sqrt (1 - x ^ 2) : ℂ)

theorem upperBoundaryRoot_continuous : Continuous upperBoundaryRoot := by
  unfold upperBoundaryRoot
  fun_prop

theorem upperBoundaryRoot_spec (x : ℝ) (hx : -1 < x) :
    upperBoundaryRoot x ^ 2 - 2 * (x : ℂ) * upperBoundaryRoot x + 1 = 0 ∧
      ‖upperBoundaryRoot x‖ ≤ 1 ∧ upperBoundaryRoot x ∈ Complex.slitPlane ∧
      (((upperBoundaryRoot x).re = x ∧ (upperBoundaryRoot x).im ≤ 0) ∨
        ((upperBoundaryRoot x).im = 0 ∧ (upperBoundaryRoot x).re ≤ x ∧ 1 ≤ x)) := by
  by_cases hx1 : x ≤ 1
  · have hxsq : x ^ 2 ≤ 1 := by nlinarith
    have hz : Real.sqrt (x ^ 2 - 1) = 0 := Real.sqrt_eq_zero_of_nonpos (by linarith)
    have hs : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 := Real.sq_sqrt (by linarith)
    have hsC : (Real.sqrt (1 - x ^ 2) : ℂ) ^ 2 = 1 - (x : ℂ) ^ 2 := by exact_mod_cast hs
    have hre : (upperBoundaryRoot x).re = x := by simp [upperBoundaryRoot, hz]
    have him : (upperBoundaryRoot x).im = -Real.sqrt (1 - x ^ 2) := by
      simp [upperBoundaryRoot, hz]
    have hnorm : ‖upperBoundaryRoot x‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
      nlinarith
    refine ⟨?_, by nlinarith [norm_nonneg (upperBoundaryRoot x)], ?_,
      Or.inl ⟨hre, by rw [him]; exact neg_nonpos.mpr (Real.sqrt_nonneg _)⟩⟩
    · unfold upperBoundaryRoot
      rw [hz, Complex.ofReal_zero, sub_zero]
      linear_combination (Real.sqrt (1 - x ^ 2) : ℂ) ^ 2 * Complex.I_sq - hsC
    · apply Complex.mem_slitPlane_iff.mpr
      by_cases hp : 0 < x
      · exact Or.inl (by rw [hre]; exact hp)
      · right
        rw [him]
        apply neg_ne_zero.mpr
        apply ne_of_gt
        apply Real.sqrt_pos.mpr
        have hxp : x ≤ 0 := le_of_not_gt hp
        nlinarith
  · have hx1' : 1 < x := lt_of_not_ge hx1
    have hz : Real.sqrt (1 - x ^ 2) = 0 := Real.sqrt_eq_zero_of_nonpos (by nlinarith)
    have hs : Real.sqrt (x ^ 2 - 1) ^ 2 = x ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
    have hr : 0 < x - Real.sqrt (x ^ 2 - 1) := by
      nlinarith [Real.sqrt_nonneg (x ^ 2 - 1)]
    have hle : x - Real.sqrt (x ^ 2 - 1) ≤ 1 := by
      nlinarith [Real.sqrt_nonneg (x ^ 2 - 1), sq_nonneg (x - 1)]
    have he : upperBoundaryRoot x = ((x - Real.sqrt (x ^ 2 - 1) : ℝ) : ℂ) := by
      simp [upperBoundaryRoot, hz]
    refine ⟨?_, ?_, ?_, Or.inr ?_⟩
    · rw [he]
      have hp : (x - Real.sqrt (x ^ 2 - 1)) ^ 2 -
          2 * x * (x - Real.sqrt (x ^ 2 - 1)) + 1 = 0 := by nlinarith
      exact_mod_cast hp
    · rw [he, Complex.norm_real, Real.norm_of_nonneg hr.le]
      exact hle
    · rw [he]
      exact Complex.ofReal_mem_slitPlane.mpr hr
    · simp only [he, Complex.ofReal_im, Complex.ofReal_re, true_and]
      exact ⟨sub_le_self _ (Real.sqrt_nonneg _), hx1'.le⟩

theorem upperBoundaryRoot_ne_zero (x : ℝ) (hx : -1 < x) : upperBoundaryRoot x ≠ 0 := by
  intro hz
  have hp := (upperBoundaryRoot_spec x hx).1
  rw [hz] at hp
  norm_num at hp

theorem root_partner_distance_identity (x : ℝ) (r a : ℂ) :
    ‖r - (2 * (x : ℂ) - a)‖ ^ 2 - ‖r - a‖ ^ 2 =
      4 * (x - a.re) * (x - r.re) + 4 * a.im * r.im := by
  norm_num [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem upperBoundaryRoot_partner_farther (x : ℝ) (hx : -1 < x) (r : ℂ)
    (hr : ‖r‖ ≤ 1) (hi : r.im ≤ 0) :
    ‖r - upperBoundaryRoot x‖ ≤ ‖r - (2 * (x : ℂ) - upperBoundaryRoot x)‖ := by
  have hd := root_partner_distance_identity x r (upperBoundaryRoot x)
  have hnonneg : 0 ≤ 4 * (x - (upperBoundaryRoot x).re) * (x - r.re) +
      4 * (upperBoundaryRoot x).im * r.im := by
    rcases (upperBoundaryRoot_spec x hx).2.2.2 with ⟨hre, him⟩ | ⟨him, hre, hxx⟩
    · rw [hre, sub_self, mul_zero, zero_mul, zero_add]
      nlinarith [mul_nonneg_of_nonpos_of_nonpos him hi]
    · rw [him, mul_zero, zero_mul, add_zero]
      have hrr : r.re ≤ 1 := Complex.re_le_norm r |>.trans hr
      exact mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hre))
        (sub_nonneg.mpr (hrr.trans hxx))
  nlinarith [norm_nonneg (r - upperBoundaryRoot x),
    norm_nonneg (r - (2 * (x : ℂ) - upperBoundaryRoot x))]

/-- One square-root modulus works on the entire real boundary x>-1,
including x=1 and the real left-arc segment x>1. -/
theorem upperEdgeRoot_boundary_holder (x : ℝ) (hx : -1 < x) (W : ℂ) (hW : 0 < W.im) :
    ‖upperEdgeRoot W - upperBoundaryRoot x‖ ^ 2 ≤ 2 * ‖W - (x : ℂ)‖ := by
  let r := upperEdgeRoot W
  let a := upperBoundaryRoot x
  have hr : ‖r‖ ≤ 1 := (upperEdgeRoot_norm_lt_one hW).le
  have hi : r.im ≤ 0 := (upperEdgeRoot_im_neg (Or.inl hW)).le
  have hcomp := upperBoundaryRoot_partner_farther x hx r hr hi
  have hp := upperEdgeRoot_polynomial W
  have ha := (upperBoundaryRoot_spec x hx).1
  have hfactor : (r - a) * (r - (2 * (x : ℂ) - a)) = 2 * (W - (x : ℂ)) * r := by
    dsimp only [r, a]
    linear_combination hp - ha
  change ‖r - a‖ ^ 2 ≤ 2 * ‖W - (x : ℂ)‖
  calc
    _ ≤ ‖r - a‖ * ‖r - (2 * (x : ℂ) - a)‖ := by
      nlinarith [norm_nonneg (r - a)]
    _ = 2 * ‖W - (x : ℂ)‖ * ‖r‖ := by
      have ht : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
      simpa only [norm_mul, ht] using congrArg norm hfactor
    _ ≤ _ := by nlinarith [norm_nonneg (W - (x : ℂ))]

theorem upperEdgeRoot_tendsto_boundary (x : ℝ) (hx : -1 < x) :
    Tendsto upperEdgeRoot (𝓝[{W : ℂ | 0 < W.im}] (x : ℂ)) (𝓝 (upperBoundaryRoot x)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hδ : 0 < ε ^ 2 / 2 := by positivity
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds (x : ℂ) hδ),
    self_mem_nhdsWithin] with W hdist hW
  have hb := upperEdgeRoot_boundary_holder x hx W hW
  rw [mem_ball, dist_eq_norm] at hdist
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (upperEdgeRoot W - upperBoundaryRoot x)]

def upperPhysicalPhase (W : ℂ) : ℂ := Complex.I * Complex.log (upperEdgeRoot W)

def upperBoundaryPhase (x : ℝ) : ℂ := Complex.I * Complex.log (upperBoundaryRoot x)

theorem upperPhysicalPhase_analyticAt (W : ℂ) (hW : 0 < W.im) :
    AnalyticAt ℂ upperPhysicalPhase W := by
  have hr := upperEdgeRoot_analyticAt (edge_discriminant_slit (Or.inl hW))
  have hs : upperEdgeRoot W ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inr (ne_of_lt (upperEdgeRoot_im_neg (Or.inl hW))))
  exact analyticAt_const.mul (hr.clog hs)

theorem upperPhysicalPhase_tendsto_boundary (x : ℝ) (hx : -1 < x) :
    Tendsto upperPhysicalPhase (𝓝[{W : ℂ | 0 < W.im}] (x : ℂ)) (𝓝 (upperBoundaryPhase x)) := by
  exact tendsto_const_nhds.mul
    ((continuousAt_clog (upperBoundaryRoot_spec x hx).2.2.1).tendsto.comp
      (upperEdgeRoot_tendsto_boundary x hx))

theorem upperBoundaryPhase_continuousAt (x : ℝ) (hx : -1 < x) :
    ContinuousAt upperBoundaryPhase x :=
  continuousAt_const.mul
    ((continuousAt_clog (upperBoundaryRoot_spec x hx).2.2.1).comp
      upperBoundaryRoot_continuous.continuousAt)

theorem upperPhysicalPhase_exp (W : ℂ) :
    Complex.exp (-(upperPhysicalPhase W * Complex.I)) = upperEdgeRoot W := by
  have he : -(upperPhysicalPhase W * Complex.I) = Complex.log (upperEdgeRoot W) := by
    unfold upperPhysicalPhase
    linear_combination -(Complex.log (upperEdgeRoot W)) * Complex.I_sq
  rw [he, Complex.exp_log (upperEdgeRoot_ne_zero W)]

theorem upperPhysicalPhase_cos (W : ℂ) : Complex.cos (upperPhysicalPhase W) = W := by
  have hr := upperEdgeRoot_ne_zero W
  have hp := upperEdgeRoot_polynomial W
  have he := upperPhysicalPhase_exp W
  have hi : Complex.exp (upperPhysicalPhase W * Complex.I) = (upperEdgeRoot W)⁻¹ := by
    rw [← he, Complex.exp_neg, inv_inv]
  rw [Complex.cos, hi, neg_mul, he]
  field_simp
  linear_combination hp

end IsingBulk.AnisoF002.Isotropic
