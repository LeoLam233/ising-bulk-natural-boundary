import IsingBulk.AnisoF002.C03.IsotropicProtectedPair

/-!
# Contraction of the actual complete pair on the limiting right arc

The proof retains the complete pair. It combines the original dispersion
with the two sine-ratio contractions, including both apparent endpoint
denominators through the already defined analytic fill.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open Set

theorem real_sine_pair_defect (a b : ℝ) :
    Real.sin ((a + b) / 2) ^ 2 - Real.sin ((a - b) / 2) ^ 2 = Real.sin a * Real.sin b := by
  rw [Real.sin_sq_eq_half_sub, Real.sin_sq_eq_half_sub]
  rw [show 2 * ((a + b) / 2) = a + b by ring,
    show 2 * ((a - b) / 2) = a - b by ring, Real.cos_add, Real.cos_sub]
  ring

theorem real_sine_pair_ratio_bound (a b : ℝ) (hs : 0 ≤ Real.sin a * Real.sin b) :
    |Real.sin ((a - b) / 2) / Real.sin ((a + b) / 2)| ≤ 1 := by
  by_cases hz : Real.sin ((a + b) / 2) = 0
  · simp [hz]
  · rw [abs_div, div_le_one (abs_pos.mpr hz)]
    apply sq_le_sq.mp
    have h := real_sine_pair_defect a b
    linarith

theorem real_dispersion_pair_sine_identity (S wa wb φa φb : ℝ)
    (ha : Real.cos wa + Real.cos φa = S)
    (hb : Real.cos wb + Real.cos φb = S) :
    Real.sin ((wa + wb) / 2) * Real.sin ((wa - wb) / 2) +
      Real.sin ((φa + φb) / 2) * Real.sin ((φa - φb) / 2) = 0 := by
  have hw := Real.cos_sub_cos wa wb
  have hp := Real.cos_sub_cos φa φb
  linear_combination (1 / 2 : ℝ) * (hw + hp - ha + hb)

theorem real_dispersion_pair_product (S wa wb φa φb : ℝ)
    (ha : Real.cos wa + Real.cos φa = S)
    (hb : Real.cos wb + Real.cos φb = S)
    (hw : Real.sin ((wa + wb) / 2) ≠ 0)
    (hp : Real.sin ((φa + φb) / 2) ≠ 0) :
    -(Real.sin ((wa - wb) / 2) / Real.sin ((φa + φb) / 2)) ^ 2 =
      (Real.sin ((wa - wb) / 2) / Real.sin ((wa + wb) / 2)) *
        (Real.sin ((φa - φb) / 2) / Real.sin ((φa + φb) / 2)) := by
  have h := real_dispersion_pair_sine_identity S wa wb φa φb ha hb
  field_simp [hw, hp]
  linear_combination -Real.sin ((wa - wb) / 2) * h

theorem real_filled_complete_pair_bound (S wa wb φa φb : ℝ)
    (hwa : -Real.pi < wa ∧ wa ≤ 0) (hwb : -Real.pi < wb ∧ wb ≤ 0)
    (hpa : 0 ≤ φa ∧ φa < Real.pi) (hpb : 0 ≤ φb ∧ φb < Real.pi)
    (ha : Real.cos wa + Real.cos φa = S)
    (hb : Real.cos wb + Real.cos φb = S) :
    |if Real.sin ((φa + φb) / 2) = 0 then
        -(Real.sin ((φa - φb) / 2) / Real.sin ((wa + wb) / 2)) ^ 2
      else -(Real.sin ((wa - wb) / 2) / Real.sin ((φa + φb) / 2)) ^ 2| ≤ 1 := by
  split_ifs with hp
  · have hzero := (Real.sin_eq_zero_iff_of_lt_of_lt
        (x := (φa + φb) / 2) (by linarith [hpa.1, hpb.1, Real.pi_pos])
        (by linarith [hpa.2, hpb.2])).mp hp
    have hφa : φa = 0 := by linarith [hpa.1, hpb.1]
    have hφb : φb = 0 := by linarith [hpa.1, hpb.1]
    simp [hφa, hφb]
  · by_cases hw : Real.sin ((wa + wb) / 2) = 0
    · have hzero := (Real.sin_eq_zero_iff_of_lt_of_lt
          (x := (wa + wb) / 2) (by linarith [hwa.1, hwb.1])
          (by linarith [hwa.2, hwb.2, Real.pi_pos])).mp hw
      have hwa0 : wa = 0 := by linarith [hwa.2, hwb.2]
      have hwb0 : wb = 0 := by linarith [hwa.2, hwb.2]
      simp [hwa0, hwb0]
    · rw [real_dispersion_pair_product S wa wb φa φb ha hb hw hp, abs_mul]
      have hws := mul_nonneg_of_nonpos_of_nonpos
        (Real.sin_nonpos_of_nonpos_of_neg_pi_le hwa.2 hwa.1.le)
        (Real.sin_nonpos_of_nonpos_of_neg_pi_le hwb.2 hwb.1.le)
      have hps := mul_nonneg
        (Real.sin_nonneg_of_nonneg_of_le_pi hpa.1 hpa.2.le)
        (Real.sin_nonneg_of_nonneg_of_le_pi hpb.1 hpb.2.le)
      have h₁ := real_sine_pair_ratio_bound wa wb hws
      have h₂ := real_sine_pair_ratio_bound φa φb hps
      calc
        _ ≤ 1 * 1 := mul_le_mul h₁ h₂ (abs_nonneg _) (by norm_num)
        _ = 1 := one_mul 1

/-- Every actual complete right pair has modulus at most one, including
the branch pair and the zero-angle pair. -/
theorem inversePairFilled_real_right_norm_le_one (S wa wb : ℝ)
    (hS : 0 < S ∧ S < 2)
    (hwa : wa ∈ Icc (-rightBranchEndpoint S) 0)
    (hwb : wb ∈ Icc (-rightBranchEndpoint S) 0) :
    ‖inversePairFilled explicitRightInverse
      ((S : ℂ), (rightArcCoordinate S wa : ℂ), (rightArcCoordinate S wb : ℂ))‖ ≤ 1 := by
  have ha := explicitRightInverse_on_right_arc S wa hS hwa
  have hb := explicitRightInverse_on_right_arc S wb hS hwb
  have hφa : (rightArcCoordinate S wa : ℂ) - (wa : ℂ) = (rightArcPhase S wa : ℂ) := by
    simp [rightArcCoordinate]
  have hφb : (rightArcCoordinate S wb : ℂ) - (wb : ℂ) = (rightArcPhase S wb : ℂ) := by
    simp [rightArcCoordinate]
  have he : inversePairFilled explicitRightInverse
      ((S : ℂ), (rightArcCoordinate S wa : ℂ), (rightArcCoordinate S wb : ℂ)) =
      ((if Real.sin ((rightArcPhase S wa + rightArcPhase S wb) / 2) = 0 then
        -(Real.sin ((rightArcPhase S wa - rightArcPhase S wb) / 2) /
          Real.sin ((wa + wb) / 2)) ^ 2 else
        -(Real.sin ((wa - wb) / 2) /
          Real.sin ((rightArcPhase S wa + rightArcPhase S wb) / 2)) ^ 2 : ℝ) : ℂ) := by
    unfold inversePairFilled inversePairOriginal inversePairAlternative
    rw [ha, hb, hφa, hφb]
    simp only [← Complex.ofReal_add, ← Complex.ofReal_sub,
      ← Complex.ofReal_ofNat, ← Complex.ofReal_div, ← Complex.ofReal_sin,
      Complex.ofReal_eq_zero]
    split_ifs <;> push_cast <;> rfl
  rw [he, Complex.norm_real, Real.norm_eq_abs]
  apply real_filled_complete_pair_bound S wa wb (rightArcPhase S wa) (rightArcPhase S wb)
  · exact ⟨lt_of_lt_of_le (neg_lt_neg (rightBranchEndpoint_lt_pi S hS.1)) hwa.1, hwa.2⟩
  · exact ⟨lt_of_lt_of_le (neg_lt_neg (rightBranchEndpoint_lt_pi S hS.1)) hwb.1, hwb.2⟩
  · exact rightArcPhase_range S wa hS.1
  · exact rightArcPhase_range S wb hS.1
  · rw [rightArcPhase_cos S wa hS hwa]
    ring
  · rw [rightArcPhase_cos S wb hS hwb]
    ring

end IsingBulk.AnisoF002.Isotropic
