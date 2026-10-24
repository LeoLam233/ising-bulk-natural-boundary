import IsingBulk.Anisotropic.NegativeDominance.ConstrainedBetaKernel
import IsingBulk.Anisotropic.NegativeDominance.PeriodNormalization

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm

theorem constrainedBetaValue_rescale {N j : ℕ} (hN : 0<N) {τ u : ℝ}
    (hτ : 0<τ) (hu : 0<u) :
    constrainedBetaValue N j u (1/(4*(N : ℝ)))=
      2^(alpha N)*(τ/u)^(j+1-alpha N)*constrainedBetaValue N j τ (1/(2*(N : ℝ))) := by
  have hNp : (0 : ℝ)<N := by exact_mod_cast hN
  unfold constrainedBetaValue
  simp only [div_pow,one_pow,mul_pow]
  rw [show (4 : ℝ)=2*2 by norm_num,mul_pow]
  field_simp

theorem centralDensity_ne_zero (Bn rootBn : ℂ) (s : ℝ) {N : ℕ}
    (hN : 0<N) (hB : Bn≠0) (hr : rootBn≠0) (hs : s≠0) :
    centralDensity Bn rootBn s N≠0 := by
  unfold centralDensity
  apply div_ne_zero
  · exact mul_ne_zero (by norm_num) (div_ne_zero (pow_ne_zero _ hB) hr)
  · have hn : (N : ℂ)≠0 := by exact_mod_cast hN.ne'
    have hfac : (N.factorial : ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero N
    have hp : (Real.pi : ℂ)≠0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hsc : (s : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hs
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hn hfac)
      (pow_ne_zero _ (mul_ne_zero (by norm_num) hp))) (pow_ne_zero _ (by norm_num))) (pow_ne_zero _ hsc)

/-- Exact modulus normalization of the complete constrained beta period to M.
There is no common-phase assumption. -/
theorem first_beta_value_eq_model_norm (Bn rootBn H : ℂ) (s : ℝ)
    {N : ℕ} (ho : Odd N) (hN : 3≤N) (j : ℕ) (hj : alpha N≤j)
    (hB : Bn≠0) (hr : rootBn≠0) (hH : H≠0) (hs : s≠0) :
    constrainedBetaValue N j (tau N) (1/(2*(N : ℝ)))=
      ‖H‖^(alpha N)/(2*‖centralDensity Bn rootBn s N‖)*‖model Bn rootBn H s N j‖ := by
  have he := central_period_eq_model Bn rootBn H s ho hN j hj
  have hp := shapePeriod_factorial ho hN j hj (tau N) (1/(2*(N : ℝ)))
    (tau_pos N (by omega)) (by positivity)
  change shapePeriod (N-1) j (tau N) ((1/(2*(N : ℝ)) : ℝ) : ℂ)=
    (constrainedBetaValue N j (tau N) (1/(2*(N : ℝ))) : ℂ) at hp
  rw [hp] at he
  have hn := congrArg norm he
  have hv := constrainedBetaValue_pos (by omega : 0<N) j (tau_pos N (by omega))
    (by positivity : 0<1/(2*(N : ℝ)))
  simp only [norm_mul,zpow_neg,zpow_natCast,norm_inv,norm_pow,Complex.norm_ofNat,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hv] at hn
  have hcn := norm_ne_zero_iff.mpr (centralDensity_ne_zero Bn rootBn s (N := N) (by omega) hB hr hs)
  have hhn := norm_ne_zero_iff.mpr hH
  rw [←hn]
  field_simp

end
end IsingBulk.Anisotropic.NegativeDominance
