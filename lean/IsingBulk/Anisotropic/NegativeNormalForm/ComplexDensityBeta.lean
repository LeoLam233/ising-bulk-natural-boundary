import IsingBulk.Anisotropic.NegativeNormalForm.TruncatedShapeBeta
import IsingBulk.Anisotropic.NegativeCycles.ModelPeriodNorm

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open MeasureTheory Set IsingBulk.First IsingBulk.Anisotropic.NegativeDominance
open IsingBulk.Anisotropic.NegativeCycles
open scoped BigOperators

theorem cutoff_exponential_bound (theta : ℝ) (rho : ℂ) (x C L : ℝ)
    (hC : 0≤C) (hx : 0≤x) (htheta : ‖theta‖≤1)
    (hsupport : theta≠0 → x<L)
    (hrho : theta≠0 → ‖rho-1‖≤Real.exp (C*(Real.sqrt x+x))-1) :
    ‖(theta:ℂ)*(rho-1)‖≤truncatedExponential C L x := by
  by_cases ht : theta=0
  · simp only [ht,Complex.ofReal_zero,zero_mul,norm_zero]
    exact truncatedExponential_nonneg C L x hC
  · have herr := hrho ht
    have hn : ‖(theta:ℂ)*(rho-1)‖≤‖rho-1‖ := by
      rw [norm_mul,Complex.norm_real]
      exact (mul_le_mul_of_nonneg_right htheta (norm_nonneg _)).trans_eq (one_mul _)
    by_cases hp : 0<x
    · rw [truncatedExponential,indicator_of_mem (show x∈Ioo 0 L from ⟨hp,hsupport ht⟩)]
      exact hn.trans herr
    · have hz : x=0 := le_antisymm (le_of_not_gt hp) hx
      rw [hz,Real.sqrt_zero,add_zero,mul_zero,Real.exp_zero,sub_self] at herr
      exact (hn.trans herr).trans (truncatedExponential_nonneg C L x hC)

/-- Domination of the actual complex quadratic-kernel density error by its
positive beta expectation. No replacement of the complex period is made. -/
theorem complexDensityError_beta_bound {n : ℕ} (ho : Odd (n+1)) (hn : 2≤n)
    (j K : ℕ) (hj : 4*alpha (n+1)+4≤j) (hKj : K≤j-j/2)
    (tau : ℝ) (c : ℂ) (C L : ℝ) (ht : 0<tau) (hc : 0<c.re) (hC : 0≤C)
    (hL : 1≤L) (hK : C*(Real.sqrt L+L)≤(K:ℝ)*Real.log 2)
    (f : (Fin n→ℝ)→ℂ)
    (hf : ∀q,‖f q‖≤truncatedExponential C L
      (c.re*(∑ i : Fin (n+1),shapeExtend q i^2)/tau)) :
    ‖∫q : Fin n→ℝ,f q*quadraticModelKernel n j tau c q‖≤
      (‖c‖/c.re)^alpha (n+1)*
      (expErrorConstant C 1*(Real.sqrt ((alpha (n+1):ℝ)/((j:ℝ)-alpha (n+1)))+
        (alpha (n+1):ℝ)/((j:ℝ)-alpha (n+1)))+
        (2:ℝ)^(-((j-K-j/2:ℕ):ℤ))*4^alpha (n+1))*‖shapePeriod n j tau c‖ := by
  have hji : alpha (n+1)≤j := by omega
  have hi := truncatedShapeBeta_integrable ho hn j hji tau c.re ht hc C L hC
  have hbound (q : Fin n→ℝ) : ‖f q*quadraticModelKernel n j tau c q‖≤
      truncatedExponential C L (c.re*(∑ i : Fin (n+1),shapeExtend q i^2)/tau)*
        constrainedBetaKernel n j tau c.re q := by
    have hk := quadraticModelKernel_tail_pointwise (a:=j) (j:=j) le_rfl tau ht c hc 0
      le_rfl q (constrainedSquaredRadius_nonneg q)
    simp only [Nat.sub_self,pow_zero,one_mul] at hk
    rw [norm_mul]
    exact mul_le_mul (hf q) hk (norm_nonneg _) (truncatedExponential_nonneg C L _ hC)
  have hint := norm_integral_le_of_norm_le hi (Filter.Eventually.of_forall hbound)
  have herr := truncatedShapeBeta_error ho hn j K hj hKj tau c.re C L ht hc hC hL hK
  have hval := constrainedBetaValue_pos (show 0<n+1 by omega) j ht hc
  have herror := (div_le_iff₀ hval).mp herr
  apply hint.trans
  apply herror.trans_eq
  rw [betaValue_eq_complex_period_norm ho hn j hji tau ht c hc]
  ring

end
end IsingBulk.Anisotropic.NegativeNormalForm
