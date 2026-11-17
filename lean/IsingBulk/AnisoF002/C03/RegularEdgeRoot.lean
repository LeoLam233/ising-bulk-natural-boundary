import IsingBulk.AnisoF002.Geometry.CanonicalRootAlgebra
import IsingBulk.AnisoF002.RegularTail.SchurContraction
import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# One analytic spectral branch along a complete regular edge circle

The formula W - i sqrt(1-W²) is analytic simultaneously on the upper
half-plane and across the open real interval (-1,1).  It supplies the
boundary unit root and all other real-angle small roots with one branch.
The compact-neighborhood argument can therefore retain strict Schur
contraction without incorrectly imposing norm ≤ 1 off the physical side.
-/

namespace IsingBulk.AnisoF002.RegularTail
noncomputable section
open IsingBulk.AnisoF002.Geometry Set
open scoped Topology

def upperEdgeRoot (W : ℂ) : ℂ := W - Complex.I * Complex.sqrt (1 - W ^ 2)

def upperEdgeRegion (W : ℂ) : Prop :=
  0 < W.im ∨ (W.im = 0 ∧ |W.re| < 1)

theorem edge_discriminant_slit {W : ℂ} (hW : upperEdgeRegion W) :
    1 - W ^ 2 ∈ Complex.slitPlane := by
  apply Complex.mem_slitPlane_iff.mpr
  rcases hW with him | ⟨him, hre⟩
  · by_cases hx : W.re = 0
    · left
      simp only [Complex.sub_re, Complex.one_re, pow_two, Complex.mul_re, hx,
        zero_mul, zero_sub, sub_neg_eq_add]
      positivity
    · right
      simp only [Complex.sub_im, Complex.one_im, pow_two, Complex.mul_im, zero_sub]
      have hxy : W.re * W.im ≠ 0 := mul_ne_zero hx (ne_of_gt him)
      intro he
      apply hxy
      nlinarith
  · left
    simp only [Complex.sub_re, Complex.one_re, pow_two, Complex.mul_re, him,
      zero_mul, sub_zero]
    have hs := (sq_lt_one_iff_abs_lt_one W.re).mpr hre
    nlinarith

theorem sqrt_re_pos_of_slit {a : ℂ} (ha : a ∈ Complex.slitPlane) :
    0 < (Complex.sqrt a).re := by
  rw [Complex.sqrt, Complex.cpow_inv_two_re]
  apply Real.sqrt_pos.mpr
  rcases Complex.mem_slitPlane_iff.mp ha with hr | hi
  · have hn := norm_nonneg a
    linarith
  · have hh := Complex.abs_re_lt_norm.mpr hi
    have ha' := neg_abs_le a.re
    linarith

theorem edge_sqrt_re_gt_im {W : ℂ} (hW : upperEdgeRegion W) :
    W.im < (Complex.sqrt (1 - W ^ 2)).re := by
  let a := Complex.sqrt (1 - W ^ 2)
  have ha : 0 < a.re := sqrt_re_pos_of_slit (edge_discriminant_slit hW)
  have hs : a ^ 2 = 1 - W ^ 2 := by
    simpa only [a, Complex.sqrt] using Complex.cpow_ofNat_inv_pow (1 - W ^ 2) 2
  have hre := congrArg Complex.re hs
  have him := congrArg Complex.im hs
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, zero_sub] at hre him
  have hp : a.re * a.im = -W.re * W.im := by nlinarith [him]
  have hp2 := congrArg (fun x : ℝ => x ^ 2) hp
  have hid : (a.re ^ 2 - W.im ^ 2) * (a.re ^ 2 + W.re ^ 2) = a.re ^ 2 := by
    linear_combination a.re ^ 2 * hre + hp2
  have hfactor : 0 < a.re ^ 2 + W.re ^ 2 := by positivity
  have hdiff : 0 < a.re ^ 2 - W.im ^ 2 := by
    apply (mul_pos_iff_of_pos_right hfactor).mp
    rw [hid]
    exact sq_pos_of_pos ha
  have hnonneg : 0 ≤ W.im := by rcases hW with h | ⟨h, _⟩ <;> linarith
  change W.im < a.re
  nlinarith

theorem upperEdgeRoot_im_neg {W : ℂ} (hW : upperEdgeRegion W) :
    (upperEdgeRoot W).im < 0 := by
  have hh := edge_sqrt_re_gt_im hW
  simp only [upperEdgeRoot, Complex.sub_im, Complex.mul_im, Complex.I_re,
    Complex.I_im, zero_mul, one_mul, zero_add]
  linarith

theorem upperEdgeRoot_polynomial (W : ℂ) :
    upperEdgeRoot W ^ 2 - 2 * W * upperEdgeRoot W + 1 = 0 := by
  have hs : Complex.sqrt (1 - W ^ 2) ^ 2 = 1 - W ^ 2 := by
    simpa only [Complex.sqrt] using Complex.cpow_ofNat_inv_pow (1 - W ^ 2) 2
  unfold upperEdgeRoot
  linear_combination (Complex.sqrt (1 - W ^ 2)) ^ 2 * Complex.I_sq - hs

theorem upperEdgeRoot_ne_zero (W : ℂ) : upperEdgeRoot W ≠ 0 := by
  intro he
  have hp := upperEdgeRoot_polynomial W
  rw [he] at hp
  norm_num at hp

theorem upperEdgeRoot_analyticAt {W : ℂ} (hW : 1 - W ^ 2 ∈ Complex.slitPlane) :
    AnalyticAt ℂ upperEdgeRoot W := by
  have hd : AnalyticAt ℂ (fun z : ℂ => 1 - z ^ 2) W :=
    analyticAt_const.sub (analyticAt_id.pow 2)
  have hs : AnalyticAt ℂ (fun z : ℂ => Complex.sqrt (1 - z ^ 2)) W := by
    simpa only [Complex.sqrt] using
      hd.cpow (g := fun _ : ℂ => (2⁻¹ : ℂ)) analyticAt_const hW
  exact analyticAt_id.sub (analyticAt_const.mul hs)

theorem reciprocal_root_imag_identity {W r : ℂ}
    (hp : r ^ 2 - 2 * W * r + 1 = 0) (hr : r ≠ 0) :
    2 * W.im * Complex.normSq r = r.im * (Complex.normSq r - 1) := by
  have he : 2 * W = r + r⁻¹ := by
    apply (mul_right_cancel₀ hr)
    field_simp
    linear_combination -hp
  have hi := congrArg Complex.im he
  norm_num [Complex.mul_im, Complex.add_im, Complex.inv_im] at hi
  have hn : Complex.normSq r ≠ 0 := ne_of_gt (Complex.normSq_pos.mpr hr)
  have hh := congrArg (fun x : ℝ => x * Complex.normSq r) hi
  field_simp at hh
  linear_combination hh

theorem upperEdgeRoot_norm_le_one {W : ℂ} (hW : upperEdgeRegion W) :
    ‖upperEdgeRoot W‖ ≤ 1 := by
  let r := upperEdgeRoot W
  have him : r.im < 0 := upperEdgeRoot_im_neg hW
  have hn : 0 < Complex.normSq r := Complex.normSq_pos.mpr (upperEdgeRoot_ne_zero W)
  have he := reciprocal_root_imag_identity (upperEdgeRoot_polynomial W) (upperEdgeRoot_ne_zero W)
  change 2 * W.im * Complex.normSq r = r.im * (Complex.normSq r - 1) at he
  have hw : 0 ≤ W.im := by rcases hW with h | ⟨h, _⟩ <;> linarith
  have hleft : 0 ≤ 2 * W.im * Complex.normSq r := by positivity
  have hn1 : Complex.normSq r ≤ 1 := by nlinarith
  rw [Complex.normSq_eq_norm_sq] at hn1
  change ‖r‖ ≤ 1
  nlinarith [norm_nonneg r]

theorem upperEdgeRoot_norm_lt_one {W : ℂ} (hW : 0 < W.im) :
    ‖upperEdgeRoot W‖ < 1 := by
  let r := upperEdgeRoot W
  have him : r.im < 0 := upperEdgeRoot_im_neg (Or.inl hW)
  have hn : 0 < Complex.normSq r := Complex.normSq_pos.mpr (upperEdgeRoot_ne_zero W)
  have he := reciprocal_root_imag_identity (upperEdgeRoot_polynomial W) (upperEdgeRoot_ne_zero W)
  change 2 * W.im * Complex.normSq r = r.im * (Complex.normSq r - 1) at he
  have hleft : 0 < 2 * W.im * Complex.normSq r := by positivity
  have hn1 : Complex.normSq r < 1 := by nlinarith
  rw [Complex.normSq_eq_norm_sq] at hn1
  change ‖r‖ < 1
  nlinarith [norm_nonneg r]

theorem upperEdgeRoot_pair_denominator {W V : ℂ}
    (hW : upperEdgeRegion W) (hV : upperEdgeRegion V) :
    1 - upperEdgeRoot W * upperEdgeRoot V ≠ 0 :=
  schur_denominator_ne_zero (upperEdgeRoot_norm_le_one hW) (upperEdgeRoot_norm_le_one hV)
    (mul_pos_of_neg_of_neg (upperEdgeRoot_im_neg hW) (upperEdgeRoot_im_neg hV))

theorem upperEdgeRoot_schur_lt_one {W V : ℂ}
    (hW : upperEdgeRegion W) (hV : upperEdgeRegion V) :
    ‖schur (upperEdgeRoot W) (upperEdgeRoot V)‖ < 1 :=
  schur_norm_lt_one (upperEdgeRoot_norm_le_one hW) (upperEdgeRoot_norm_le_one hV)
    (mul_pos_of_neg_of_neg (upperEdgeRoot_im_neg hW) (upperEdgeRoot_im_neg hV))

theorem edge_dispersion_upperRegion {b : ℝ} {A : ℂ}
    (hb : |b| < 1) (hA : 0 < A.im) (q : ℝ) :
    upperEdgeRegion ((b : ℂ) + A * (1 - Complex.cos (q : ℂ))) := by
  have hc : 0 ≤ 1 - Real.cos q := sub_nonneg.mpr (Real.cos_le_one q)
  by_cases hz : 1 - Real.cos q = 0
  · right
    have he : (b : ℂ) + A * (1 - Complex.cos (q : ℂ)) = (b : ℂ) := by
      rw [← Complex.ofReal_cos, ← Complex.ofReal_one, ← Complex.ofReal_sub, hz]
      simp
    simp only [he, Complex.ofReal_im, Complex.ofReal_re, true_and]
    exact hb
  · left
    have hp : 0 < 1 - Real.cos q := lt_of_le_of_ne hc (Ne.symm hz)
    simpa [← Complex.ofReal_cos] using mul_pos hA hp

end
end IsingBulk.AnisoF002.RegularTail
