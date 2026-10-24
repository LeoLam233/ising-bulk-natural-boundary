import IsingBulk.Anisotropic.NegativeNormalForm.ComplexBetaPrime
import IsingBulk.Anisotropic.NegativeNormalForm.RadialPeriod

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open MeasureTheory Set

theorem complexRadialBeta_unit (m k : ℕ) (h : ℂ) (hh : 0<h.re) :
    (∫ r in Ioi (0:ℝ), (r:ℂ)^(2*m+1)/(1+h*(r:ℂ)^2)^(m+k+2))=
      (m.factorial:ℂ)*k.factorial/(2*h^(m+1)*(m+k+1).factorial) := by
  have he := integral_comp_rpow_Ioi
    (fun x : ℝ => (x:ℂ)^m/(1+h*(x:ℂ))^(m+k+2)) (by norm_num : (2:ℝ)≠0)
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2),show (2:ℝ)-1=1 by norm_num,
    Real.rpow_one,Real.rpow_two,Complex.real_smul,Complex.ofReal_mul,
    Complex.ofReal_ofNat,Complex.ofReal_pow] at he
  have hid (r : ℝ) : (2:ℂ)*r*(((r:ℂ)^2)^m/(1+h*(r:ℂ)^2)^(m+k+2))=
      2*((r:ℂ)^(2*m+1)/(1+h*(r:ℂ)^2)^(m+k+2)) := by
    rw [←pow_mul,pow_succ]
    ring
  simp only [hid] at he
  rw [integral_const_mul,complexBetaPrime_factorial m k h hh] at he
  calc
    _ = (((m.factorial:ℂ)*k.factorial/(m+k+1).factorial)/h^(m+1))/2 := by
      linear_combination he/2
    _ = _ := by ring

theorem complexRadialBeta_scaled (m k : ℕ) (tau : ℝ) (ht : 0<tau)
    (c : ℂ) (hc : 0<c.re) :
    (∫ r in Ioi (0:ℝ), (r:ℂ)^(2*m+1)/((tau:ℂ)+c*(r:ℂ)^2)^(m+k+2))=
      (m.factorial:ℂ)*k.factorial/
        (2*c^(m+1)*(tau:ℂ)^(k+1)*(m+k+1).factorial) := by
  let s := Real.sqrt tau
  have hs : 0<s := Real.sqrt_pos.mpr ht
  have hs2 : (s:ℂ)^2=(tau:ℂ) := by exact_mod_cast (Real.sq_sqrt ht.le)
  have ht0 : (tau:ℂ)≠0 := by exact_mod_cast ht.ne'
  have hp (r : ℝ) : ((s*r:ℝ):ℂ)^(2*m+1)/((tau:ℂ)+c*((s*r:ℝ):ℂ)^2)^(m+k+2)=
      ((s:ℂ)^(2*m+1)/(tau:ℂ)^(m+k+2))*
        ((r:ℂ)^(2*m+1)/(1+c*(r:ℂ)^2)^(m+k+2)) := by
    have hd : (tau:ℂ)+c*((s*r:ℝ):ℂ)^2=(tau:ℂ)*(1+c*(r:ℂ)^2) := by
      rw [Complex.ofReal_mul,mul_pow,hs2]
      ring
    rw [hd,Complex.ofReal_mul]
    simp only [mul_pow,div_eq_mul_inv,mul_inv_rev]
    ring
  have hi := integral_comp_mul_left_Ioi'
    (fun r : ℝ => (r:ℂ)^(2*m+1)/((tau:ℂ)+c*(r:ℂ)^2)^(m+k+2)) 0 hs
  simp only [mul_zero,Complex.real_smul] at hi
  rw [←hi]
  simp_rw [hp]
  rw [integral_const_mul,complexRadialBeta_unit m k c hc]
  have he : (s:ℂ)*(s:ℂ)^(2*m+1)=(tau:ℂ)^(m+1) := by
    rw [←pow_succ',show 2*m+1+1=2*(m+1) by omega,pow_mul,hs2]
  calc
    _ = ((s:ℂ)*(s:ℂ)^(2*m+1))/(tau:ℂ)^(m+k+2)*
        ((m.factorial:ℂ)*k.factorial/(2*c^(m+1)*(m+k+1).factorial)) := by ring
    _ = _ := by
      rw [he,show m+k+2=(m+1)+(k+1) by omega,pow_add]
      field_simp [ht0]
      simp only [pow_add,pow_succ]
      ring

theorem complexRadialBeta_order (a j : ℕ) (ha : 0<a) (haj : a≤j)
    (tau : ℝ) (ht : 0<tau) (c : ℂ) (hc : 0<c.re) :
    (∫ r in Ioi (0:ℝ), (r:ℂ)^(2*a-1)/((tau:ℂ)+c*(r:ℂ)^2)^(j+1))=
      ((a-1).factorial:ℂ)*(j-a).factorial/
        (2*c^a*(tau:ℂ)^(j+1-a)*j.factorial) := by
  obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
  obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le haj
  subst a
  subst j
  have he1 : 2*m.succ-1=2*m+1 := by omega
  have he2 : m.succ+k+1=m+k+2 := by omega
  have he3 : m.succ+k-m.succ=k := by omega
  have he4 : m.succ+k+1-m.succ=k+1 := by omega
  have he5 : m.succ+k=m+k+1 := by omega
  rw [he3,he4,he1,he2,Nat.succ_sub_one,he5]
  exact complexRadialBeta_scaled m k tau ht c hc

end
end IsingBulk.Anisotropic.NegativeNormalForm
