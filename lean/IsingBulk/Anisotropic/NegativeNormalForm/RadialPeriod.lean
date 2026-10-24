import IsingBulk.Anisotropic.NegativeNormalForm.BetaPeriod
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! The exact radial beta period, with the quadratic substitution Jacobian
and positive anisotropic scaling proved explicitly. -/
namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open MeasureTheory Set

theorem radialBeta_unit (m k : ℕ) :
    (∫ r in Ioi (0 : ℝ), r^(2*m+1)/(1+r^2)^(m+k+2)) =
      (m.factorial : ℝ) * k.factorial / (2*(m+k+1).factorial) := by
  have h := integral_comp_rpow_Ioi (fun x : ℝ => x^m/(1+x)^(m+k+2))
    (by norm_num : (2 : ℝ) ≠ 0)
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ)<2), show (2 : ℝ)-1=1 by norm_num, Real.rpow_one,
    Real.rpow_two, smul_eq_mul] at h
  have he (r : ℝ) : 2*r * ((r^2)^m/(1+r^2)^(m+k+2)) =
      2 * (r^(2*m+1)/(1+r^2)^(m+k+2)) := by
    rw [← pow_mul, pow_succ]
    ring
  simp_rw [he] at h
  rw [integral_const_mul, betaPrime_factorial] at h
  linear_combination h / 2

theorem radialBeta_scaled (m k : ℕ) (tau c : ℝ) (ht : 0 < tau) (hc : 0 < c) :
    (∫ r in Ioi (0 : ℝ), r^(2*m+1)/(tau+c*r^2)^(m+k+2)) =
      (m.factorial : ℝ) * k.factorial /
        (2*c^(m+1)*tau^(k+1)*(m+k+1).factorial) := by
  let s := Real.sqrt (tau/c)
  have hs : 0 < s := Real.sqrt_pos.mpr (div_pos ht hc)
  have hs2 : s^2 = tau/c := Real.sq_sqrt (div_nonneg ht.le hc.le)
  have hp (r : ℝ) : (s*r)^(2*m+1)/(tau+c*(s*r)^2)^(m+k+2) =
      (s^(2*m+1)/tau^(m+k+2)) * (r^(2*m+1)/(1+r^2)^(m+k+2)) := by
    have hd : tau+c*(s*r)^2 = tau*(1+r^2) := by
      rw [mul_pow, hs2]
      field_simp
    rw [hd]
    simp only [mul_pow, div_eq_mul_inv, mul_inv_rev]
    ring
  have h := integral_comp_mul_left_Ioi'
    (fun r : ℝ => r^(2*m+1)/(tau+c*r^2)^(m+k+2)) 0 hs
  simp only [mul_zero, smul_eq_mul] at h
  rw [← h]
  simp_rw [hp]
  rw [integral_const_mul, radialBeta_unit]
  have he : s*s^(2*m+1) = (tau/c)^(m+1) := by
    rw [← pow_succ', show 2*m+1+1=2*(m+1) by omega, pow_mul, hs2]
  calc
    _ = (s*s^(2*m+1))/tau^(m+k+2) *
        ((m.factorial : ℝ)*k.factorial/(2*(m+k+1).factorial)) := by ring
    _ = _ := by
      rw [he, div_pow, show m+k+2=(m+1)+(k+1) by omega, pow_add]
      field_simp
      ring


theorem radialBeta_order (a j : ℕ) (ha : 0 < a) (haj : a ≤ j)
    (tau c : ℝ) (ht : 0 < tau) (hc : 0 < c) :
    (∫ r in Ioi (0 : ℝ), r^(2*a-1)/(tau+c*r^2)^(j+1)) =
      ((a-1).factorial : ℝ) * (j-a).factorial /
        (2*c^a*tau^(j+1-a)*j.factorial) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le haj
  subst a
  subst j
  have he1 : 2*m.succ-1 = 2*m+1 := by omega
  have he2 : m.succ+k+1 = m+k+2 := by omega
  have he3 : m.succ+k-m.succ = k := by omega
  have he4 : m.succ+k+1-m.succ = k+1 := by omega
  have he5 : m.succ+k = m+k+1 := by omega
  rw [he3, he4, he1, he2, Nat.succ_sub_one, he5]
  exact radialBeta_scaled m k tau c ht hc

end
end IsingBulk.Anisotropic.NegativeNormalForm
