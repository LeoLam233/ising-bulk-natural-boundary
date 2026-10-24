import IsingBulk.Anisotropic.NegativeNormalForm.BetaExponential
import IsingBulk.Anisotropic.NegativeDominance.ResonanceScale

/-! Dimension-uniform constants and the explicit n/√j+n²/j beta scale. -/
namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open MeasureTheory Set
open IsingBulk.Anisotropic.NegativeDominance

theorem alpha_pos_and_twice_le (n : ℕ) (hn : 3≤n) :
    0<alpha n ∧ 2*alpha n≤n*n := by
  have h : 9≤n*n := by nlinarith
  unfold alpha
  omega

theorem beta_moment_dimension_bound (n j : ℕ) (hn : 3≤n) (hj : 2*alpha n≤j) :
    (alpha n : ℝ)/((j : ℝ)-alpha n) ≤ (n : ℝ)^2/j := by
  obtain ⟨ha,han⟩ := alpha_pos_and_twice_le n hn
  have ha' : (0 : ℝ)<alpha n := by exact_mod_cast ha
  have hj' : 2*(alpha n : ℝ)≤j := by exact_mod_cast hj
  have han' : 2*(alpha n : ℝ)≤(n : ℝ)^2 := by exact_mod_cast (show 2*alpha n≤n^2 by simpa [pow_two] using han)
  have hj0 : (0 : ℝ)<j := by linarith
  have hd : 0<(j : ℝ)-alpha n := by linarith
  calc
    _ ≤ 2*(alpha n : ℝ)/j := by
      apply (div_le_div_iff₀ hd hj0).2
      nlinarith
    _ ≤ _ := div_le_div_of_nonneg_right han' hj0.le

theorem beta_sqrt_moment_dimension_bound (n j : ℕ) (hn : 3≤n) (hj : 2*alpha n≤j) :
    Real.sqrt ((alpha n : ℝ)/((j : ℝ)-alpha n)) ≤ (n : ℝ)/Real.sqrt j := by
  have h := Real.sqrt_le_sqrt (beta_moment_dimension_bound n j hn hj)
  simpa only [Real.sqrt_div (by positivity : 0≤(n : ℝ)^2), Real.sqrt_sq (by positivity : 0≤(n : ℝ))] using h

/-- The concrete small-x exponential beta error is O(n/√j+n²/j), with the
same displayed constant for every dimension. -/
theorem beta_exponential_inner_dimension (n j : ℕ) (hn : 3≤n) (hj : 2*alpha n≤j)
    (C delta : ℝ) (hC : 0≤C) :
    (∫ x in Ioo (0 : ℝ) delta,
      (Real.exp (C*(Real.sqrt x+x))-1)*(x^(alpha n-1)/(1+x)^(j+1))) / betaMass (alpha n) j ≤
      expErrorConstant C delta * ((n : ℝ)/Real.sqrt j+(n : ℝ)^2/j) := by
  have ha := (alpha_pos_and_twice_le n hn).1
  have haj : alpha n<j := by omega
  exact (beta_exponential_inner (alpha n) j ha haj C delta hC).trans
    (mul_le_mul_of_nonneg_left (add_le_add (beta_sqrt_moment_dimension_bound n j hn hj)
      (beta_moment_dimension_bound n j hn hj)) (mul_nonneg hC (Real.exp_pos _).le))

/-- Uniform conversion from nQ to the beta coordinate x, using actual τₙ. -/
theorem density_exponent_beta_bound (n : ℕ) (hn : 0<n) (C x : ℝ) (hC : 0≤C) (hx : 0≤x) :
    C*(Real.sqrt (2*(n : ℝ)^2*tau n*x)+2*(n : ℝ)^2*tau n*x) ≤
      C*Real.pi^2*(Real.sqrt x+x) := by
  have hb := (scaled_tau_bounds n hn).2
  have hbx := mul_le_mul_of_nonneg_right hb hx
  have hs := Real.sqrt_le_sqrt hbx
  rw [Real.sqrt_mul (sq_nonneg Real.pi), Real.sqrt_sq Real.pi_pos.le] at hs
  have hlo := (scaled_tau_bounds n hn).1
  have hpi : Real.pi≤Real.pi^2 := by nlinarith [sq_nonneg (Real.pi-2)]
  have hs' : Real.sqrt (2*(n : ℝ)^2*tau n*x)≤Real.pi^2*Real.sqrt x :=
    hs.trans (mul_le_mul_of_nonneg_right hpi (Real.sqrt_nonneg x))
  have h := mul_le_mul_of_nonneg_left (add_le_add hs' hbx) hC
  nlinarith

/-- The explicit 4^α tail factor is exponentially small once α/j is small. -/
theorem beta_tail_factor_exponential (a j : ℕ) (delta : ℝ) (hd : 0<delta)
    (ha : (a : ℝ)*Real.log 4 ≤ (j : ℝ)*Real.log (1+delta)/8) :
    (1+delta)^(-((j-j/4-j/2 : ℕ) : ℤ))*4^a ≤
      Real.exp (-(j : ℝ)*Real.log (1+delta)/8) := by
  have hb : 0<1+delta := by linarith
  have hl : 0<Real.log (1+delta) := Real.log_pos (by linarith)
  have he : (j : ℝ)/4 ≤ ((j-j/4-j/2 : ℕ) : ℝ) := by
    have hnat : j≤4*(j-j/4-j/2) := by omega
    have hc : (j : ℝ)≤4*((j-j/4-j/2 : ℕ) : ℝ) := by exact_mod_cast hnat
    linarith
  have hpow (k : ℕ) (b : ℝ) (hb : 0<b) : b^k=Real.exp ((k : ℝ)*Real.log b) := by
    rw [Real.exp_nat_mul, Real.exp_log hb]
  rw [zpow_neg,zpow_natCast,hpow _ _ hb,hpow _ _ (by norm_num : (0:ℝ)<4),← Real.exp_neg,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right he hl.le
  linarith

end
end IsingBulk.Anisotropic.NegativeNormalForm
