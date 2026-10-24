import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic

namespace IsingBulk.Anisotropic.PhysicalField
noncomputable section
open Set

theorem hasDerivAt_of_odd_right_derivative {m : ℝ → ℝ} {d : ℝ}
    (hodd : ∀ h, m (-h)= -m h) (hr : HasDerivWithinAt m d (Ioi 0) 0) :
    HasDerivAt m d 0 := by
  have hr' : HasDerivWithinAt m d (Ioi 0) (-(0:ℝ)) := by simpa using hr
  have hn : HasDerivWithinAt (fun h : ℝ => -h) (-1) (Iio 0) 0 :=
    (hasDerivAt_id (0:ℝ)).neg.hasDerivWithinAt
  have hc := (hr'.comp 0 hn (fun h hh => by change h<0 at hh; change 0< -h; linarith)).neg
  have hl : HasDerivWithinAt m d (Iio 0) 0 := by
    simpa only [Function.comp_def,Pi.neg_def,hodd,neg_neg,mul_neg_one] using hc
  have hb := hr.Ici_of_Ioi.union hl.Iic_of_Iio
  have he : Ici (0:ℝ)∪Iic 0=univ := by ext x; simp only [mem_union,mem_Ici,mem_Iic,mem_univ,iff_true]; exact le_total 0 x
  rw [he] at hb
  exact hasDerivWithinAt_univ.mp hb

end
end IsingBulk.Anisotropic.PhysicalField
