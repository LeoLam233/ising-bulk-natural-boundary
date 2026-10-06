import IsingBulk.Tail.SchurContraction
import IsingBulk.Tail.SelectorDefinitions

/-! Complete-pair strictness for the compact limiting groups, including
common endpoints where an individual y factor is 0/0. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First

theorem lower_unit_reciprocal_eq {a b : ℂ} (ha : ‖a‖=1)
    (hai : a.im ≤ 0) (hbi : b.im ≤ 0) (hab : 1-a*b=0) : a=b := by
  have hp : a*b=1 := (sub_eq_zero.mp hab).symm
  have hb : b=a⁻¹ := (inv_eq_of_mul_eq_one_right hp).symm
  rw [Complex.inv_eq_conj ha] at hb
  have hi : a.im=0 := by rw [hb,Complex.conj_im] at hbi; linarith
  rw [hb]
  apply Complex.ext <;> simp [hi]

theorem complete_pair_strict_of_strict_root {a b z w s : ℂ}
    (ha : ‖a‖=1) (hb : ‖b‖=1) (hai : a.im ≤ 0) (hbi : b.im ≤ 0)
    (hz0 : z ≠ 0) (hw0 : w ≠ 0)
    (hzq : z^2-(2*sourceS s-a-a⁻¹)*z+1=0)
    (hwq : w^2-(2*sourceS s-b-b⁻¹)*w+1=0)
    (hzw : Complex.normSq (z-w) < Complex.normSq (1-z*w)) :
    ‖canceledPair a b z w‖ < 1 := by
  by_cases hab : 1-a*b=0
  · have he := lower_unit_reciprocal_eq ha hai hbi hab
    simp [canceledPair,he]
  · have hden : 1-z*w ≠ 0 := by
      intro he
      rw [he] at hzw
      simp only [map_zero] at hzw
      exact (not_lt_of_ge (Complex.normSq_nonneg _)) hzw
    have ha0 : a ≠ 0 := norm_ne_zero_iff.mp (by rw [ha]; norm_num)
    have hb0 : b ≠ 0 := norm_ne_zero_iff.mp (by rw [hb]; norm_num)
    have he := source_pair_identity ha0 hb0 hz0 hw0 hzq hwq hab hden
    change ‖-(a-b)^2*z*w/(a*b*(1-z*w)^2)‖ < 1
    rw [← he,norm_mul]
    have hy : ‖pairKernel a b‖ ≤ 1 := schur_norm_le ha.le hb.le
      (mul_nonneg_of_nonpos_of_nonpos hai hbi)
    have hz : ‖pairKernel z w‖ < 1 := schur_norm_lt_of_normSq_lt hzw
    exact (mul_le_of_le_one_right (norm_nonneg _) hy).trans_lt hz

theorem complete_pair_strict_left {a b z w s : ℂ}
    (ha : ‖a‖=1) (hb : ‖b‖=1) (hai : a.im ≤ 0) (hbi : b.im ≤ 0)
    (hz0 : z ≠ 0) (hw0 : w ≠ 0)
    (hzq : z^2-(2*sourceS s-a-a⁻¹)*z+1=0)
    (hwq : w^2-(2*sourceS s-b-b⁻¹)*w+1=0)
    (hz : ‖z‖<1) (hw : ‖w‖<1) (hzi : z.im≤0) (hwi : w.im≤0) :
    ‖canceledPair a b z w‖ < 1 :=
  complete_pair_strict_of_strict_root ha hb hai hbi hz0 hw0 hzq hwq
    (schur_normSq_lt_of_interior hz hw (mul_nonneg_of_nonpos_of_nonpos hzi hwi))

theorem complete_pair_strict_right {a b z w s : ℂ}
    (ha : ‖a‖=1) (hb : ‖b‖=1) (hai : a.im ≤ 0) (hbi : b.im ≤ 0)
    (hz0 : z ≠ 0) (hw0 : w ≠ 0)
    (hzq : z^2-(2*sourceS s-a-a⁻¹)*z+1=0)
    (hwq : w^2-(2*sourceS s-b-b⁻¹)*w+1=0)
    (hz : ‖z‖≤1) (hw : ‖w‖≤1) (hzi : z.im<0) (hwi : w.im<0) :
    ‖canceledPair a b z w‖ < 1 :=
  complete_pair_strict_of_strict_root ha hb hai hbi hz0 hw0 hzq hwq
    (schur_normSq_lt_of_same_half hz hw (mul_pos_of_neg_of_neg hzi hwi))

end
end IsingBulk.Tail
