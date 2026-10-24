import IsingBulk.Anisotropic.RegularEdges.ComplexAngular
import IsingBulk.Anisotropic.NegativeNormalForm.ResonantKernel

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.Anisotropic.RegularEdges IsingBulk.Anisotropic.NegativeNormalForm
open scoped BigOperators

theorem exp_sinh_denominator (g : ℂ) :
    1-Complex.exp (-g)^2=2*Complex.exp (-g)*Complex.sinh g := by
  have hm : Complex.exp g*Complex.exp (-g)=1 := by rw [←Complex.exp_add]; simp
  rw [Complex.sinh]
  linear_combination -hm

theorem rootOneBody_exp_neg (g : ℂ) :
    2*Complex.exp (-g)/(1-Complex.exp (-g)^2)=(Complex.sinh g)⁻¹ := by
  rw [exp_sinh_denominator,div_mul_eq_div_div,
    div_self (mul_ne_zero (by norm_num) (Complex.exp_ne_zero _)),one_div]

theorem angularRootPair_exp_neg (a b q t : ℂ) :
    angularRootPair (Complex.exp (-a)) (Complex.exp (-b)) q t=
      (Complex.sin ((q-t)/2)/Complex.sinh ((a+b)/2))^2 := by
  let e := Complex.exp (-((a+b)/2))
  have he : e≠0 := Complex.exp_ne_zero _
  have hp : Complex.exp (-a)*Complex.exp (-b)=e^2 := by
    dsimp [e]
    rw [pow_two,←Complex.exp_add,←Complex.exp_add]
    congr 1
    ring
  unfold angularRootPair
  rw [show 4*Complex.exp (-a)*Complex.exp (-b)=4*(Complex.exp (-a)*Complex.exp (-b)) by ring,hp]
  rw [exp_sinh_denominator]
  change 4*e^2*Complex.sin ((q-t)/2)^2/(2*e*Complex.sinh ((a+b)/2))^2=_
  rw [show 4*e^2*Complex.sin ((q-t)/2)^2=(2*e*Complex.sin ((q-t)/2))^2 by ring,←div_pow]
  rw [mul_div_mul_left _ _ (mul_ne_zero (by norm_num) he)]

theorem rootProduct_exp_neg {N : ℕ} (g : Fin N→ℂ) :
    (∏i,Complex.exp (-g i))=Complex.exp (-(∑i,g i)) := by
  rw [←Complex.exp_sum,Finset.sum_neg_distrib]

theorem rootKernel_exp_neg {N : ℕ} (g : Fin N→ℂ) :
    (1+∏i,Complex.exp (-g i))/(1-∏i,Complex.exp (-g i))=
      (Complex.exp (∑i,g i)+1)/(Complex.exp (∑i,g i)-1) := by
  rw [rootProduct_exp_neg,Complex.exp_neg]
  let E := Complex.exp (∑i,g i)
  have he : E≠0 := Complex.exp_ne_zero _
  change (1+E⁻¹)/(1-E⁻¹)=(E+1)/(E-1)
  rw [show 1+E⁻¹=(E+1)/E by field_simp,show 1-E⁻¹=(E-1)/E by field_simp]
  rw [div_div_div_comm,div_self he,div_one]

end IsingBulk.Anisotropic.NegativeCycles
