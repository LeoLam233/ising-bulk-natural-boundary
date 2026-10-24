import IsingBulk.Anisotropic.NegativeNormalForm.RadialPeriod

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open MeasureTheory Set

theorem weightedRadialBeta (m j : ℕ) (tau c : ℝ) (ht : 0<tau) (hc : 0<c)
    (w : ℝ → ℝ) :
    (∫ r in Ioi (0:ℝ), r^(2*m+1)*w (c*r^2/tau)/(tau+c*r^2)^(j+1))=
      (tau/c)^(m+1)/(2*tau^(j+1))*
        (∫ x in Ioi (0:ℝ), x^m*w x/(1+x)^(j+1)) := by
  let f : ℝ → ℝ := fun x => x^m*w (c*x/tau)/(tau+c*x)^(j+1)
  let s := tau/c
  have hs : 0<s := div_pos ht hc
  have hcs : c*s=tau := by dsimp [s]; field_simp
  have hp (x : ℝ) : f (s*x)=s^m/tau^(j+1)*(x^m*w x/(1+x)^(j+1)) := by
    have ha : c*(s*x)/tau=x := by rw [←mul_assoc,hcs]; field_simp
    have hd : tau+c*(s*x)=tau*(1+x) := by rw [←mul_assoc,hcs]; ring
    dsimp [f]
    rw [ha,hd,mul_pow,mul_pow]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  have hscale := integral_comp_mul_left_Ioi' f 0 hs
  simp only [mul_zero,smul_eq_mul] at hscale
  have hscaled : (∫ x in Ioi (0:ℝ), f x)=s^(m+1)/tau^(j+1)*
      (∫ x in Ioi (0:ℝ), x^m*w x/(1+x)^(j+1)) := by
    rw [←hscale]
    simp_rw [hp]
    rw [integral_const_mul,pow_succ]
    ring
  have hquad := integral_comp_rpow_Ioi f (by norm_num : (2:ℝ)≠0)
  norm_num only [abs_of_pos (by norm_num : (0:ℝ)<2),show (2:ℝ)-1=1 by norm_num,
    Real.rpow_one,Real.rpow_two,smul_eq_mul] at hquad
  have he (r : ℝ) : 2*r*f (r^2)=2*(r^(2*m+1)*w (c*r^2/tau)/(tau+c*r^2)^(j+1)) := by
    dsimp [f]
    rw [←pow_mul,pow_succ]
    ring
  simp_rw [he] at hquad
  rw [integral_const_mul,hscaled] at hquad
  dsimp [s] at hquad
  linear_combination hquad/2

theorem weightedRadialBeta_order (a j : ℕ) (ha : 0<a) (tau c : ℝ)
    (ht : 0<tau) (hc : 0<c) (w : ℝ → ℝ) :
    (∫ r in Ioi (0:ℝ), r^(2*a-1)*w (c*r^2/tau)/(tau+c*r^2)^(j+1))=
      (tau/c)^a/(2*tau^(j+1))*
        (∫ x in Ioi (0:ℝ), x^(a-1)*w x/(1+x)^(j+1)) := by
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
  simpa only [Nat.succ_sub_one,show 2*m.succ-1=2*m+1 by omega] using
    weightedRadialBeta m j tau c ht hc w

end
end IsingBulk.Anisotropic.NegativeNormalForm
