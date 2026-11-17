import IsingBulk.AnisoF002.C03.RegularFilledMatchingBounds
import IsingBulk.AnisoF002.C03.RegularIsotropicPairGap
import IsingBulk.AnisoF002.C03.RegularIsotropicMixedGap
import IsingBulk.AnisoF002.RegularTail.SinePair

/-!
# Actual complete pairs on the same angular semicircle

The balanced deformation moves upper angles inward and lower angles
outward. In either case the two angular Schur factors occupy the same
norm side, so the complete pair is contractive. Reciprocal angular
collisions are included by the literal canceled formula.
-/

namespace IsingBulk.AnisoF002.Isotropic
noncomputable section
open Set
open scoped Topology
open IsingBulk.AnisoF002.RegularTail IsingBulk.AnisoF002.RegularTail.C03

theorem fixedOccupancyAngle_exp_norm (η τ ρ υ θ : ℝ) :
    ‖Complex.exp (fixedOccupancyAngle η τ ρ υ θ * Complex.I)‖ =
      Real.exp (τ * (ρ * lowerPeriodicBump η θ - υ * upperPeriodicBump η θ)) := by
  rw [Complex.norm_exp]
  simp [fixedOccupancyAngle, Complex.mul_re]

theorem fixedOccupancyAngle_exp_im (η τ ρ υ θ : ℝ) :
    (Complex.exp (fixedOccupancyAngle η τ ρ υ θ * Complex.I)).im =
      Real.exp (τ * (ρ * lowerPeriodicBump η θ - υ * upperPeriodicBump η θ)) * Real.sin θ := by
  rw [Complex.exp_im]
  simp [fixedOccupancyAngle, Complex.mul_re, Complex.mul_im]

theorem fixedOccupancyAngle_exp_upper (η τ ρ υ θ : ℝ)
    (hη : 0 < η) (hτ : 0 ≤ τ) (hυ : 0 ≤ υ) (hθ : 0 ≤ Real.sin θ) :
    ‖Complex.exp (fixedOccupancyAngle η τ ρ υ θ * Complex.I)‖ ≤ 1 ∧
      0 ≤ (Complex.exp (fixedOccupancyAngle η τ ρ υ θ * Complex.I)).im := by
  have hm : lowerPeriodicBump η θ = 0 := by
    apply upperPeriodicBump_zero hη
    rw [Real.sin_neg]
    linarith
  rw [fixedOccupancyAngle_exp_norm, fixedOccupancyAngle_exp_im]
  constructor
  · apply Real.exp_le_one_iff.mpr
    rw [hm, mul_zero, zero_sub]
    exact mul_nonpos_of_nonneg_of_nonpos hτ (neg_nonpos.mpr
      (mul_nonneg hυ (upperPeriodicBump_bounds η θ).1))
  · exact mul_nonneg (Real.exp_pos _).le hθ

theorem fixedOccupancyAngle_exp_lower (η τ ρ υ θ : ℝ)
    (hη : 0 < η) (hτ : 0 ≤ τ) (hρ : 0 ≤ ρ) (hθ : Real.sin θ ≤ 0) :
    1 ≤ ‖Complex.exp (fixedOccupancyAngle η τ ρ υ θ * Complex.I)‖ ∧
      (Complex.exp (fixedOccupancyAngle η τ ρ υ θ * Complex.I)).im ≤ 0 := by
  have hp := upperPeriodicBump_zero hη (hθ.trans hη.le)
  rw [fixedOccupancyAngle_exp_norm, fixedOccupancyAngle_exp_im]
  constructor
  · apply Real.one_le_exp
    rw [hp, mul_zero, sub_zero]
    exact mul_nonneg hτ (mul_nonneg hρ (lowerPeriodicBump_bounds η θ).1)
  · exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hθ

theorem isotropic_complete_pair_same_side (S w v : ℂ)
    (hW : 0 < (isotropicDispersion (S, w)).im) (hV : 0 < (isotropicDispersion (S, v)).im)
    (him : 0 ≤ (Complex.exp (w * Complex.I)).im * (Complex.exp (v * Complex.I)).im)
    (hn : (‖Complex.exp (w * Complex.I)‖ ≤ 1 ∧ ‖Complex.exp (v * Complex.I)‖ ≤ 1) ∨
      (1 ≤ ‖Complex.exp (w * Complex.I)‖ ∧ 1 ≤ ‖Complex.exp (v * Complex.I)‖)) :
    ‖canceledPair 1 (isotropicInteriorRoot (S, w)) (isotropicInteriorRoot (S, v))
      (Complex.exp (w * Complex.I)) (Complex.exp (v * Complex.I))‖ ≤ 1 := by
  by_cases hd : 1 - Complex.exp (w * Complex.I) * Complex.exp (v * Complex.I) = 0
  · have he := same_norm_side_reciprocal_forces_equal him hn hd
    simp only [canceledPair, he, sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, zero_div, norm_zero]
    norm_num
  · have hp (u : ℂ) : isotropicInteriorRoot (S, u) ^ 2 - 2 *
        (S - 1 * (Complex.exp (u * Complex.I) + (Complex.exp (u * Complex.I))⁻¹) / 2) *
          isotropicInteriorRoot (S, u) + 1 = 0 := by
      rw [one_mul, complex_cos_exp_inverse]
      exact isotropicInteriorRoot_polynomial _
    have he := schur_pair_eq_canceled (S := (1 : ℂ)) (T := 1) (A := S)
      (r := isotropicInteriorRoot (S, w)) (s := isotropicInteriorRoot (S, v))
      (by norm_num) (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
      (upperEdgeRoot_pair_denominator (Or.inl hW) (Or.inl hV)) hd
      (by simpa only [one_mul] using reciprocal_polynomial_exp_form (Complex.exp_ne_zero _) (hp w))
      (by simpa only [one_mul] using reciprocal_polynomial_exp_form (Complex.exp_ne_zero _) (hp v))
    simp only [div_one] at he
    rw [← he, norm_mul]
    have hr := schur_norm_le_one_closed_lower _ _
      (upperEdgeRoot_norm_le_one (Or.inl hW)) (upperEdgeRoot_norm_le_one (Or.inl hV))
      (upperEdgeRoot_im_neg (Or.inl hW)).le (upperEdgeRoot_im_neg (Or.inl hV)).le
    have ha := schur_norm_le_one_same_norm_side him hn
    exact (mul_le_mul hr ha (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

theorem actual_balanced_same_side_pair {N : ℕ} (hN : 0 < N)
    (S : ℂ) (hS : 0 < S.im) (η τ : ℝ) (hη : 0 < η) (hτ : 0 ≤ τ)
    (θ : Fin N → ℝ) (i j : Fin N)
    (hside : (0 ≤ Real.sin (θ i) ∧ 0 ≤ Real.sin (θ j)) ∨
      (Real.sin (θ i) ≤ 0 ∧ Real.sin (θ j) ≤ 0)) :
    ‖canceledPair 1 (isotropicInteriorRoot (S, actualHomotopyAngle η τ 1 θ i))
      (isotropicInteriorRoot (S, actualHomotopyAngle η τ 1 θ j))
      (Complex.exp (actualHomotopyAngle η τ 1 θ i * Complex.I))
      (Complex.exp (actualHomotopyAngle η τ 1 θ j * Complex.I))‖ ≤ 1 := by
  have hρ := (actualUpperOccupancy_mem_Icc hN η θ).1
  have hυ := (actualLowerOccupancy_mem_Icc hN η θ).1
  apply isotropic_complete_pair_same_side S (actualHomotopyAngle η τ 1 θ i)
    (actualHomotopyAngle η τ 1 θ j)
    (actual_balanced_homotopy_sheet S hS η τ 1 hη hτ zero_le_one θ i)
    (actual_balanced_homotopy_sheet S hS η τ 1 hη hτ zero_le_one θ j)
  · rcases hside with hside | hside
    · have hi := fixedOccupancyAngle_exp_upper η τ (actualUpperOccupancy η θ) (actualLowerOccupancy η θ) (θ i) hη hτ hυ hside.1
      have hj := fixedOccupancyAngle_exp_upper η τ (actualUpperOccupancy η θ) (actualLowerOccupancy η θ) (θ j) hη hτ hυ hside.2
      simpa only [actualHomotopyAngle_eq_fixedOccupancy, one_mul] using mul_nonneg hi.2 hj.2
    · have hi := fixedOccupancyAngle_exp_lower η τ (actualUpperOccupancy η θ) (actualLowerOccupancy η θ) (θ i) hη hτ hρ hside.1
      have hj := fixedOccupancyAngle_exp_lower η τ (actualUpperOccupancy η θ) (actualLowerOccupancy η θ) (θ j) hη hτ hρ hside.2
      simpa only [actualHomotopyAngle_eq_fixedOccupancy, one_mul] using
        mul_nonneg_of_nonpos_of_nonpos hi.2 hj.2
  · rcases hside with hside | hside
    · left
      have hi := fixedOccupancyAngle_exp_upper η τ (actualUpperOccupancy η θ) (actualLowerOccupancy η θ) (θ i) hη hτ hυ hside.1
      have hj := fixedOccupancyAngle_exp_upper η τ (actualUpperOccupancy η θ) (actualLowerOccupancy η θ) (θ j) hη hτ hυ hside.2
      simpa only [actualHomotopyAngle_eq_fixedOccupancy, one_mul] using And.intro hi.1 hj.1
    · right
      have hi := fixedOccupancyAngle_exp_lower η τ (actualUpperOccupancy η θ) (actualLowerOccupancy η θ) (θ i) hη hτ hρ hside.1
      have hj := fixedOccupancyAngle_exp_lower η τ (actualUpperOccupancy η θ) (actualLowerOccupancy η θ) (θ j) hη hτ hρ hside.2
      simpa only [actualHomotopyAngle_eq_fixedOccupancy, one_mul] using And.intro hi.1 hj.1

theorem complex_sin_norm_le_exp_abs_im (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  have he := congrArg norm (Complex.two_sin z)
  rw [norm_mul, Complex.norm_two, norm_mul, Complex.norm_I, mul_one] at he
  have hs := norm_sub_le (Complex.exp (-z * Complex.I)) (Complex.exp (z * Complex.I))
  rw [← he, Complex.norm_exp, Complex.norm_exp] at hs
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_sub, neg_neg] at hs
  have h1 := Real.exp_le_exp.mpr (le_abs_self z.im)
  have h2 := Real.exp_le_exp.mpr (neg_le_abs z.im)
  linarith

theorem canceledPair_norm_bound_by_gap {r s w v : ℂ}
    (hr : ‖r‖ ≤ 1) (hs : ‖s‖ ≤ 1) (hw : |w.im| ≤ 1) (hv : |v.im| ≤ 1) :
    ‖canceledPair 1 r s (Complex.exp (w * Complex.I)) (Complex.exp (v * Complex.I))‖ ≤
      (4 * Real.exp 1 ^ 2) / ‖1 - r * s‖ ^ 2 := by
  have hhalf : |((w - v) / 2).im| ≤ 1 := by
    simp only [Complex.div_ofNat_im, Complex.sub_im, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h := abs_sub (w.im) (v.im)
    linarith
  have hsin := (complex_sin_norm_le_exp_abs_im ((w - v) / 2)).trans (Real.exp_le_exp.mpr hhalf)
  rw [canceledPair_eq_sinePair, sinePairCoefficient, norm_mul, norm_div, norm_pow,
    norm_mul, norm_mul, norm_mul, norm_one, mul_one, norm_pow, Complex.norm_ofNat]
  have hm : 4 * ‖r‖ * ‖s‖ * ‖Complex.sin ((w - v) / 2)‖ ^ 2 ≤ 4 * Real.exp 1 ^ 2 := by
    calc
      _ ≤ 4 * 1 * 1 * (Real.exp 1) ^ 2 := by gcongr
      _ = _ := by ring
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right hm (sq_nonneg _)

end
end IsingBulk.AnisoF002.Isotropic
