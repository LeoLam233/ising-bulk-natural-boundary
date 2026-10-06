import IsingBulk.First.GlobalResidueRoot

/-! The global root and the actual local lowerArccos phase are the same object. -/
namespace IsingBulk.First
noncomputable section
open IsingBulk.Branch

theorem interiorRoot_eq_exp_lowerArccos (W : ℂ) :
    interiorRoot W = Complex.exp (-Complex.I*lowerArccos W) := by
  have he : -Complex.I*lowerArccos W = -Complex.log (inverseCosineRoot W) := by
    unfold lowerArccos
    have hi := Complex.I_mul_I
    calc
      _ = (Complex.I*Complex.I)*Complex.log (inverseCosineRoot W) := by ring
      _ = _ := by rw [hi]; ring
  rw [he, Complex.exp_neg, Complex.exp_log (inverseCosineRoot_ne_zero W)]
  rfl

theorem globalRoot_eq_exp_lowerArccos (s y : ℂ) :
    globalRoot s y = Complex.exp (-Complex.I*lowerArccos (sourceW s y)) :=
  interiorRoot_eq_exp_lowerArccos _

end
end IsingBulk.First
