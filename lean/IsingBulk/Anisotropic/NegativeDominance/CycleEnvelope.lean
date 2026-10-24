import IsingBulk.Anisotropic.NegativeCycles.ActualCycleComparison
import IsingBulk.Anisotropic.NegativeDominance.GaussianEntropyAbsorption

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section

/-- The explicit, already proved genuine Stokes error bound. -/
def cycleErrorEnvelope (ρ M c L K σ : ℝ) (m j : ℕ) : ℝ :=
  (((((2*m : ℕ) : ℝ)+1)*K*
    ((2*((M*M^m)*M^(2*m+1)*(1/2 : ℝ)^((2*m+1).choose 2))/(c*(2*m+1 : ℕ))))*
      ((8*(2*m+1 : ℕ) : ℝ)/σ)^(j+1))*
    Real.sqrt ((((2*m : ℕ) : ℝ)*L^2)^(2*m)))*(2*ρ)^(2*m)

theorem cycleErrorEnvelope_factor (ρ M c L K σ : ℝ) (m j : ℕ) :
    cycleErrorEnvelope ρ M c L K σ m j=
      (2*K/c)*(M*M^m)*M^(2*m+1)*(1/2 : ℝ)^((2*m+1).choose 2)*
        ((8*(2*m+1 : ℕ) : ℝ)/σ)^(j+1)*
        (((2*m : ℕ) : ℝ)^m*L^(2*m))*(2*ρ)^(2*m) := by
  have hs : Real.sqrt ((((2*m : ℕ) : ℝ)*L^2)^(2*m))=
      ((2*m : ℕ) : ℝ)^m*L^(2*m) := by
    rw [show ((((2*m : ℕ) : ℝ)*L^2)^(2*m))=((((2*m : ℕ) : ℝ)*L^2)^m)^2 by
      rw [←pow_mul]; congr 1; omega,Real.sqrt_sq_eq_abs,abs_of_nonneg (by positivity)]
    rw [mul_pow,←pow_mul]
  unfold cycleErrorEnvelope
  rw [hs]
  have hN : (((2*m+1 : ℕ) : ℝ))≠0 := by positivity
  push_cast at hN ⊢
  field_simp

/-- Exact logarithm, keeping the coefficient of j log N equal to one. -/
theorem cycleErrorEnvelope_log (ρ M c L K σ : ℝ) {m : ℕ} (j : ℕ)
    (hρ : 0<ρ) (hM : 0<M) (hc : 0<c) (hL : 0<L) (hK : 0<K) (hσ : 0<σ) (hm : 0<m) :
    Real.log (cycleErrorEnvelope ρ M c L K σ m j)=
      Real.log (2*K/c)+(3*(m : ℝ)+2)*Real.log M-
        (m : ℝ)*(2*m+1)*Real.log 2+
        ((j : ℝ)+1)*(Real.log (2*(m : ℝ)+1)+Real.log (8/σ))+
        (m : ℝ)*Real.log (2*(m : ℝ))+2*m*Real.log L+2*m*Real.log (2*ρ) := by
  have hmR : (m : ℝ)≠0 := by exact_mod_cast hm.ne'
  have hN : (2*(m : ℝ)+1)≠0 := by positivity
  have hchoose := Nat.cast_choose_two (K := ℝ) (2*m+1)
  push_cast at hchoose
  rw [cycleErrorEnvelope_factor]
  simp [Real.log_mul,Real.log_div,Real.log_pow,hρ.ne',hM.ne',hc.ne',hL.ne',hK.ne',hσ.ne',hmR,hN]
  rw [hchoose]
  ring

end
end IsingBulk.Anisotropic.NegativeDominance
