import IsingBulk.Joint.Isotropic.HighInverse
import Mathlib.Analysis.Complex.CoveringMap

namespace IsingBulk.Joint
noncomputable section

/-- Joukowski map appropriate to sinh, not the cosine version. -/
def sinhJoukowski (v : ℂ) : ℂ := (v - v⁻¹) / 2

theorem sinh_eq_joukowski_exp (z : ℂ) :
    Complex.sinh z = sinhJoukowski (Complex.exp z) := by
  simp only [Complex.sinh, Complex.exp_neg, sinhJoukowski]

theorem joukowski_eq_iff {v s : ℂ} (hv : v ≠ 0) :
    sinhJoukowski v = s ↔ v^2 - 2*s*v - 1 = 0 := by
  unfold sinhJoukowski
  constructor
  · intro h
    field_simp at h
    linear_combination h
  · intro h
    field_simp
    linear_combination h

theorem joukowski_injOn_outer :
    Set.InjOn sinhJoukowski {v : ℂ | 1 < ‖v‖} := by
  intro v hv w hw he
  change 1 < ‖v‖ at hv
  change 1 < ‖w‖ at hw
  have hv0 : v ≠ 0 := by intro h; norm_num [h] at hv
  have hw0 : w ≠ 0 := by intro h; norm_num [h] at hw
  have hqv := (joukowski_eq_iff hv0).mp he
  have hqw := (joukowski_eq_iff hw0).mp (rfl : sinhJoukowski w = sinhJoukowski w)
  have hprod : (v-w)*(v*w+1)=0 := by
    linear_combination w * hqv - v * hqw
  rcases mul_eq_zero.mp hprod with h | h
  · exact sub_eq_zero.mp h
  · have hmul : v*w = -1 := by linear_combination h
    have hn := congrArg norm hmul
    rw [norm_mul, norm_neg, norm_one] at hn
    have hlt : 1 < ‖v‖ * ‖w‖ := by nlinarith [mul_pos (sub_pos.mpr hv) (sub_pos.mpr hw)]
    linarith

theorem norm_joukowski_le_one_of_unit {v : ℂ} (hv : ‖v‖ = 1) :
    ‖sinhJoukowski v‖ ≤ 1 := by
  calc
    ‖sinhJoukowski v‖ = ‖v-v⁻¹‖ / 2 := by simp [sinhJoukowski]
    _ ≤ (‖v‖+‖v⁻¹‖)/2 := div_le_div_of_nonneg_right (norm_sub_le _ _) (by norm_num)
    _ = 1 := by simp [hv, norm_inv]

theorem exists_outer_joukowski_root {s : ℂ} (hs : 1 < ‖s‖) :
    ∃ v : ℂ, 1 < ‖v‖ ∧ sinhJoukowski v = s := by
  let a := s + Complex.sqrt (1+s^2)
  let b := s - Complex.sqrt (1+s^2)
  have hsq : (Complex.sqrt (1+s^2))^2 = 1+s^2 :=
    Complex.cpow_nat_inv_pow _ (by decide : (2:ℕ) ≠ 0)
  have hab : a*b = -1 := by dsimp [a,b]; linear_combination -hsq
  have ha : a ≠ 0 := by intro h; simp [h] at hab
  have hb : b ≠ 0 := by intro h; simp [h] at hab
  have hja : sinhJoukowski a = s := by
    apply (joukowski_eq_iff ha).mpr
    dsimp [a]
    linear_combination hsq
  have hjb : sinhJoukowski b = s := by
    apply (joukowski_eq_iff hb).mpr
    dsimp [b]
    linear_combination hsq
  by_cases hoa : 1 < ‖a‖
  · exact ⟨a,hoa,hja⟩
  · have hna : ‖a‖ < 1 := by
      refine lt_of_le_of_ne (le_of_not_gt hoa) ?_
      intro he
      have hh := norm_joukowski_le_one_of_unit he
      rw [hja] at hh
      linarith
    have hn : ‖a‖*‖b‖=1 := by simpa only [norm_mul,norm_neg,norm_one] using congrArg norm hab
    refine ⟨b,?_,hjb⟩
    nlinarith [norm_nonneg a, norm_nonneg b]

end
end IsingBulk.Joint
