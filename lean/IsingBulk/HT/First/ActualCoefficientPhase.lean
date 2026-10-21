import IsingBulk.HT.First.RegularOddCoefficient
import IsingBulk.HT.First.ClosedAmplitude

/-! Phase and curvature reduction of the actual regular-chart coefficient.
The original constrained period is retained; no Gaussian value or asymptotic
is assumed. The same calculation applies to both signs of the curvature. -/
namespace IsingBulk.HT.First
noncomputable section
open IsingBulk.First Complex

 theorem derivativeOrder_even {p : ℕ} (hp : Odd p) : Even (derivativeOrder p) := by
  obtain ⟨m, hm⟩ := derivativeOrder_four_dvd hp
  refine ⟨2*m, ?_⟩
  omega

 theorem neg_I_pow_derivativeOrder {p : ℕ} (hp : Odd p) :
    (-I)^derivativeOrder p = 1 := by
  obtain ⟨m, hm⟩ := derivativeOrder_four_dvd hp
  rw [hm, pow_mul]
  norm_num

/-- The literal odd period is real and positive, including for negative d. -/
theorem odd_shapePeriod_eq_positive_real {p : ℕ} (hp : Odd p) (hp3 : 3 ≤ p)
    {Q d : ℝ} (hQ : 0 < Q) (hd : d ≠ 0) :
    shapePeriod (p-1) (derivativeOrder p) Q (-I*d) =
      ((shapeAngularConstant (p-1) /
        (2*(derivativeOrder p:ℝ)*Q*|d|^derivativeOrder p):ℝ):ℂ) := by
  have hk := derivativeOrder_pos hp hp3
  have hks : derivativeOrder p-1+1 = derivativeOrder p := by omega
  have hdegree : (p-1)-1+((p-1)+1)*(p-1) = 2*(derivativeOrder p-1)+1 := by
    have h := odd_shape_radial_exponent hp hp3
    rw [show p-1+1=p by omega]
    omega
  have hJ := odd_shapePeriod_eq_radial (by omega : 1 ≤ p-1) hdegree Q (-I*d)
  rw [hks] at hJ
  have hpow : (-I*(d:ℂ))^derivativeOrder p = ((|d|^derivativeOrder p:ℝ):ℂ) := by
    rw [mul_pow, neg_I_pow_derivativeOrder hp, one_mul, ← ofReal_pow,
      curvature_power_eq_abs hp]
  rw [hJ, odd_radial_integral _ hQ hd, hks, hpow]
  push_cast
  rfl

/-- The exact amplitude before evaluating the angular Vandermonde integral. -/
def actualAngularAmplitude (p : ℕ) (K Q d : ℝ) : ℝ :=
  (2*Real.pi)*K*((derivativeOrder p).factorial:ℝ)*Q^derivativeOrder p*
    shapeAngularConstant (p-1) /
      (2*(derivativeOrder p:ℝ)*Q*|d|^derivativeOrder p)

 theorem actual_odd_coefficient_phase {p : ℕ} (hp : Odd p) (hp3 : 3 ≤ p)
    (K theta : ℝ) {Q d : ℝ} (hQ : 0 < Q) (hd : d ≠ 0) :
    -I*((2*Real.pi:ℝ):ℂ)*(K:ℂ)*(-1:ℂ)^derivativeOrder p*
      ((derivativeOrder p).factorial:ℂ)*
      (exp (-I*theta)*(Q:ℂ))^derivativeOrder p*
      shapePeriod (p-1) (derivativeOrder p) Q (-I*d) =
    -I*exp (-I*(derivativeOrder p:ℂ)*theta)*
      (actualAngularAmplitude p K Q d:ℂ) := by
  rw [odd_shapePeriod_eq_positive_real hp hp3 hQ hd,
    (derivativeOrder_even hp).neg_one_pow, mul_pow, ← exp_nat_mul]
  have he : (derivativeOrder p:ℂ)*(-I*(theta:ℂ)) =
      -I*(derivativeOrder p:ℂ)*(theta:ℂ) := by ring
  rw [he]
  unfold actualAngularAmplitude
  push_cast
  ring

/-- The remaining real scalar after all source sine factors cancel. -/
def curvatureAmplitude (p : ℕ) (theta H : ℝ) : ℝ :=
  shapeAngularConstant (p-1)*((derivativeOrder p-1).factorial:ℝ)*
    ((p:ℝ)*Real.sin theta)^(derivativeOrder p-1) /
      (2*(p.factorial:ℝ)*Real.pi^(p-1)*|H|^derivativeOrder p)

private def normalizedChartK (p : ℕ) (B : ℝ) : ℝ :=
  (2/(p.factorial:ℝ))*(2^(p*(p-1)))⁻¹*((2*Real.pi)^p)⁻¹*(B^(p^2))⁻¹

private theorem normalizedChartK_eq {p : ℕ} (hp : Odd p) (hp3 : 3 ≤ p) (B : ℝ) :
    normalizedChartK p B =
      1/((p.factorial:ℝ)*((2:ℝ)^derivativeOrder p)^2*Real.pi^p*B^(p^2)) := by
  have hN : p-1+1=p := by omega
  have hdegree : p*(p-1)+p=p^2 := by nlinarith
  have htwo : (2:ℝ)^(p*(p-1))*(2:ℝ)^p =
      2*((2:ℝ)^derivativeOrder p)^2 := by
    rw [← pow_add, hdegree, odd_square_order hp, pow_succ,
      show 2*derivativeOrder p=derivativeOrder p*2 by omega, pow_mul]
    ring
  calc
    normalizedChartK p B =
      2/((p.factorial:ℝ)*((2:ℝ)^(p*(p-1))*(2:ℝ)^p)*Real.pi^p*B^(p^2)) := by
        simp only [normalizedChartK, mul_pow, div_eq_mul_inv, mul_inv_rev]
        ring
    _ = _ := by
      rw [htwo]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

private theorem normalized_chart_amplitude {p : ℕ} (hp : Odd p) (hp3 : 3 ≤ p)
    {B P H : ℝ} (hB : 0 < B) (hP : 0 < P) (hH : H ≠ 0) :
    actualAngularAmplitude p (normalizedChartK p B) (2*P/B) (H/(2*B^3)) =
      shapeAngularConstant (p-1)*((derivativeOrder p-1).factorial:ℝ)*
        P^(derivativeOrder p-1) /
          (2*(p.factorial:ℝ)*Real.pi^(p-1)*|H|^derivativeOrder p) := by
  have hk := derivativeOrder_pos hp hp3
  have hks : derivativeOrder p-1+1=derivativeOrder p := by omega
  have hN : p-1+1=p := by omega
  have hkR : (derivativeOrder p:ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hF : (p.factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero p
  have hT : (2:ℝ)^derivativeOrder p ≠ 0 := pow_ne_zero _ (by norm_num)
  have hAbs : |H| ≠ 0 := abs_ne_zero.mpr hH
  have hfac : ((derivativeOrder p).factorial:ℝ) =
      (derivativeOrder p:ℝ)*((derivativeOrder p-1).factorial:ℝ) := by
    have h := Nat.factorial_succ (derivativeOrder p-1)
    rw [hks] at h
    exact_mod_cast h
  have hPpow : P^derivativeOrder p = P^(derivativeOrder p-1)*P := by
    calc
      _ = P^(derivativeOrder p-1+1) := congrArg (P^·) hks.symm
      _ = _ := pow_succ _ _
  have hPipow : Real.pi^p=Real.pi^(p-1)*Real.pi := by
    calc
      _ = Real.pi^(p-1+1) := congrArg (Real.pi^·) hN.symm
      _ = _ := pow_succ _ _
  have hBpow : B^(p^2)=B*(B^derivativeOrder p)^2 := by
    rw [odd_square_order hp, pow_succ,
      show 2*derivativeOrder p=derivativeOrder p*2 by omega, pow_mul]
    ring
  have hBcube : (B^3)^derivativeOrder p=(B^derivativeOrder p)^3 := by
    rw [← pow_mul, ← pow_mul]
    congr 1
    omega
  have hd : |H/(2*B^3)|=|H|/(2*B^3) := by
    rw [abs_div, abs_of_pos (by positivity : 0 < 2*B^3)]
  rw [actualAngularAmplitude, normalizedChartK_eq hp hp3, hd]
  simp only [div_pow, mul_pow]
  rw [hBpow, hBcube, hfac, hPpow, hPipow]
  field_simp [hB.ne', hP.ne', hAbs, hkR, hF, hT, Real.pi_ne_zero]

namespace Regular

 theorem Ds_eq_exp_mul_Q (a : IsingBulk.First.RegularChartData) (p : ℕ) :
    a.Ds p = exp (-I*a.theta)*(a.Q p:ℂ) := by
  unfold IsingBulk.First.RegularChartData.Ds IsingBulk.First.RegularChartData.Q
  push_cast
  ring

 theorem curvatureNumerator_ne_zero (a : IsingBulk.First.RegularChartData) :
    curvatureNumerator a.alpha a.beta ≠ 0 :=
  mul_ne_zero a.level_ne_zero (sub_pos.mpr a.cosine_product_lt_one).ne'

 theorem oddLocalLeadingCoefficient_eq_actual_phase (a : IsingBulk.First.RegularChartData)
    {p : ℕ} (hp : Odd p) (hp3 : 3 ≤ p) :
    oddLocalLeadingCoefficient a p =
      -I*exp (-I*(derivativeOrder p:ℂ)*a.theta)*
        (actualAngularAmplitude p (a.K p) (a.Q p) a.d:ℂ) := by
  have hN : p-1+1=p := by omega
  unfold oddLocalLeadingCoefficient localLeadingCoefficient
  rw [hN, Ds_eq_exp_mul_Q]
  convert actual_odd_coefficient_phase hp hp3 (a.K p) a.theta
    (a.Q_pos (N := p) (by omega)) a.d_ne_zero using 1
  ring

 theorem actualAngularAmplitude_eq_curvature (a : IsingBulk.First.RegularChartData)
    {p : ℕ} (hp : Odd p) (hp3 : 3 ≤ p) :
    actualAngularAmplitude p (a.K p) (a.Q p) a.d =
      curvatureAmplitude p a.theta (curvatureNumerator a.alpha a.beta) := by
  have hK : a.K p=normalizedChartK p (Real.sin a.beta) := rfl
  have hQ : a.Q p=2*((p:ℝ)*Real.sin a.theta)/Real.sin a.beta := by
    unfold IsingBulk.First.RegularChartData.Q
    ring
  have hd : a.d=curvatureNumerator a.alpha a.beta/(2*Real.sin a.beta^3) := rfl
  rw [hK, hQ, hd]
  exact normalized_chart_amplitude hp hp3 a.sin_beta_pos
    (mul_pos (by exact_mod_cast (show 0 < p by omega)) a.sin_theta_pos)
    (curvatureNumerator_ne_zero a)

/-- Actual coefficient phase and amplitude for both selected prime families. -/
theorem oddLocalLeadingCoefficient_eq_curvature (a : IsingBulk.First.RegularChartData)
    {p : ℕ} (hp : Odd p) (hp3 : 3 ≤ p) :
    oddLocalLeadingCoefficient a p =
      -I*exp (-I*(derivativeOrder p:ℂ)*a.theta)*
        (curvatureAmplitude p a.theta (curvatureNumerator a.alpha a.beta):ℂ) := by
  rw [oddLocalLeadingCoefficient_eq_actual_phase a hp hp3,
    actualAngularAmplitude_eq_curvature a hp hp3]

end Regular
end
end IsingBulk.HT.First
