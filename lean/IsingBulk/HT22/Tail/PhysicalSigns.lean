import IsingBulk.HT22.Tail.ZerothIdentity

namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22

theorem constraintSign_eq_signed_exp (negative : Bool) :
    Physical.constraintSign negative=Complex.exp (-Complex.I*(Physical.constraintAngle negative:ℂ)) := by
  cases negative
  · simp [Physical.constraintSign,Physical.constraintAngle]
  · simp only [Physical.constraintSign,Physical.constraintAngle,ite_true]
    rw [show -Complex.I*(Real.pi:ℂ)=-((Real.pi:ℂ)*Complex.I) by ring,
      Complex.exp_neg,Complex.exp_pi_mul_I]
    norm_num

theorem constraintAngle_abs_le_pi (negative : Bool) : |Physical.constraintAngle negative|≤Real.pi := by
  cases negative
  · simpa [Physical.constraintAngle] using Real.pi_pos.le
  · simp only [Physical.constraintAngle,ite_true,abs_of_pos Real.pi_pos,le_refl]

end
end IsingBulk.HT22.Tail
