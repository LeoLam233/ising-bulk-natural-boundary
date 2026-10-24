import IsingBulk.Anisotropic.NegativeDominance.BetaModelComparison
import Mathlib.Analysis.Real.Pi.Bounds

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section

/-- Every higher odd winding is separated from the first by a fixed factor,
uniformly in the particle number. -/
theorem higher_winding_tau_gap (N : ℕ) (hN : 0<N) (d : ℝ)
    (hd : |d|≤Real.pi) (hw : 3*Real.pi/(N : ℝ)≤|d|) :
    2*tau N≤1-Real.cos d := by
  have hNp : (0 : ℝ)<N := by exact_mod_cast hN
  have hsq : (3*Real.pi/(N : ℝ))^2≤d^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (by positivity : 0≤3*Real.pi/(N : ℝ)) hw 2
  have hcos : 2/Real.pi^2*d^2≤1-Real.cos d := by
    linarith [Real.cos_le_one_sub_mul_cos_sq hd]
  have hfirst := (tau_bounds N hN).2
  have hpi : Real.pi^2≤16 := by nlinarith [Real.pi_lt_four,Real.pi_pos]
  calc
    2*tau N ≤ Real.pi^2/(N : ℝ)^2 := by
      calc
        _ ≤ 2*(Real.pi^2/(2*(N : ℝ)^2)) := mul_le_mul_of_nonneg_left hfirst (by norm_num)
        _ = _ := by ring
    _ ≤ 18/(N : ℝ)^2 := div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)
    _ = 2/Real.pi^2*(3*Real.pi/(N : ℝ))^2 := by field_simp; ring
    _ ≤ 2/Real.pi^2*d^2 := mul_le_mul_of_nonneg_left hsq (by positivity)
    _ ≤ _ := hcos

/-- The exact beta quotient supplies exponential higher-winding suppression;
the harmless change from Q/(2N) to the proved Q/(4N) is retained explicitly. -/
theorem higher_winding_beta_suppression {N j : ℕ} (hN : 0<N)
    (hj : 4*alpha N≤j) {u : ℝ} (hu : 2*tau N≤u) :
    constrainedBetaValue N j u (1/(4*(N : ℝ)))≤
      (1/2 : ℝ)^(j/2)*constrainedBetaValue N j (tau N) (1/(2*(N : ℝ))) := by
  have ht := tau_pos N hN
  have hup : 0<u := by linarith
  have hr : tau N/u≤(1/2 : ℝ) := (div_le_iff₀ hup).mpr (by linarith)
  have hp := pow_le_pow_left₀ (div_nonneg ht.le hup.le) hr (j+1-alpha N)
  have hsmall : (2 : ℝ)^(alpha N)*(1/2)^(j+1-alpha N)≤(1/2)^(j/2) := by
    have hak : alpha N≤j+1-alpha N := by omega
    have he : j+1-alpha N=alpha N+(j+1-alpha N-alpha N) := by omega
    rw [he,pow_add,←mul_assoc,←mul_pow]
    norm_num only [show (2 : ℝ)*(1/2)=1 by norm_num,one_pow,one_mul]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hvalue := constrainedBetaValue_pos hN j ht (by positivity : 0<1/(2*(N : ℝ)))
  rw [constrainedBetaValue_rescale hN ht hup]
  exact mul_le_mul_of_nonneg_right
    ((mul_le_mul_of_nonneg_left hp (by positivity)).trans hsmall) hvalue.le

end
end IsingBulk.Anisotropic.NegativeDominance
