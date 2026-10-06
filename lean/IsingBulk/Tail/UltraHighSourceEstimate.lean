import IsingBulk.Tail.UltraHighDerivatives
import IsingBulk.Tail.ExteriorQuantitative

/-! The displayed source ultra-high estimate, for the actual even form
factors and all fixed derivative orders, with common geometry constants. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch

theorem factorial_scaled_majorant_le_sqrt (n : ℕ) (hn : 0 < n)
    {D H : ℝ} (hD : 0 ≤ D) :
    (D*H^2)^n/(n.factorial:ℝ) ≤
      (2*(Real.exp 1*D+1)*H/Real.sqrt (2*n))^(2*n) := by
  have ht := mul_le_mul_of_nonneg_right (factorial_majorant_le_sqrt n hn hD)
    (sq_nonneg (H^n))
  convert ht using 1 <;> simp only [mul_pow,div_pow,pow_mul] <;> ring

theorem ultrahigh_source_estimate (d : LocalBranchData)
    (hcsmall : d.c₀ < Real.sin d.theta/2) :
    ∃ C₀ C delta e0 : ℝ, 0 < C₀ ∧ 0 < C ∧ 0 < delta ∧ 0 < e0 ∧ e0 ≤ 1 ∧
      ∀ n : ℕ, 0 < n → ∀ j : ℕ, ∀ e : ℝ, 0 < e → e < e0 →
        ‖iteratedDeriv j (upperFormFactor (2*n)) (radialParameter d.theta e)‖ ≤
          ((j.factorial:ℝ)*C₀/delta^j)*(e⁻¹)^(j+2)*
            (C*(Real.log (1/e)+1)/Real.sqrt (2*n))^(2*n) := by
  obtain ⟨C₀,D,delta,e0,hC,hD,hd,he0,he01,hbound⟩ :=
    ultrahigh_derivative_factorial_bound d hcsmall
  refine ⟨C₀,2*(Real.exp 1*D+1),delta,e0,hC,by positivity,hd,he0,he01,?_⟩
  intro n hn j e he heSmall
  have hp := hbound n hn j e he heSmall
  have hfac := factorial_scaled_majorant_le_sqrt n hn (H := Real.log (1/e)+1) hD.le
  apply hp.trans
  have hm := mul_le_mul_of_nonneg_left hfac
    (by positivity : 0 ≤ (j.factorial:ℝ)*C₀*(e⁻¹)^2/(delta*e)^j)
  convert hm using 1
  simp only [mul_pow,pow_add,div_eq_mul_inv,mul_inv_rev,inv_pow]
  ring

end
end IsingBulk.Tail
