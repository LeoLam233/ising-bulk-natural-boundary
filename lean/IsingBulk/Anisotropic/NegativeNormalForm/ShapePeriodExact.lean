import IsingBulk.Anisotropic.NegativeNormalForm.RadialPeriod
import IsingBulk.Anisotropic.NegativeDominance.ExactModel
import IsingBulk.Anisotropic.NegativeDominance.ResonanceScale
import IsingBulk.HT.First.GaussianAngular

/-! Exact constrained periods, retaining the independent-coordinate Jacobian.
These are actual integrals on the zero-mean hyperplane, not model assumptions. -/
namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open MeasureTheory Set IsingBulk.First
open scoped BigOperators

theorem shapePeriod_real_radial {n : ℕ} (hn : 1 ≤ n) (j : ℕ) (tau c : ℝ) :
    shapePeriod n j tau (c : ℂ) =
      (shapeAngularConstant n : ℂ) *
        ((∫ r in Ioi (0 : ℝ), r^(n-1+(n+1)*n)/(tau+c*r^2)^(j+1)) : ℝ) := by
  have h := integral_shapeVandermonde_polar hn
    (fun r => (((tau+c*r^2)^(j+1))⁻¹ : ℝ))
  simp only [Complex.real_smul, ← Complex.ofReal_mul, integral_complex_ofReal] at h
  rw [shapePeriod_eq_intrinsic]
  unfold shapePeriodIntrinsic
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_add,
    ← Complex.ofReal_div, integral_complex_ofReal]
  simp_rw [div_eq_mul_inv]
  rw [h]
  simp only [shapeAngularConstant, Complex.real_smul, Complex.ofReal_mul,
    Complex.ofReal_inv, mul_assoc]


theorem alpha_eq_derivativeOrder (p : ℕ) :
    IsingBulk.Anisotropic.NegativeDominance.alpha p = IsingBulk.HT.First.derivativeOrder p := by
  simp only [IsingBulk.Anisotropic.NegativeDominance.alpha, IsingBulk.HT.First.derivativeOrder,
    pow_two]

theorem factorialProduct_eq_amplitude {p : ℕ} (hp : 1 ≤ p) :
    IsingBulk.Anisotropic.NegativeDominance.factorialProduct p =
      IsingBulk.HT.First.factorialAmplitudeProduct p := by
  rw [IsingBulk.HT.First.factorialAmplitudeProduct_eq_fin hp]
  unfold IsingBulk.Anisotropic.NegativeDominance.factorialProduct
  rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
  have hs : (∑ r ∈ Finset.range p, r) = p.choose 2 := by
    rw [Finset.sum_range_id, Nat.choose_two_right]
  rw [hs]
  exact congrArg (fun x : ℝ => x/2^(p.choose 2))
    (Fin.prod_univ_eq_prod_range (fun r : ℕ => (r.factorial : ℝ)) p).symm

open IsingBulk.Anisotropic.NegativeDominance in
/-- The complete constrained period in (4.46), in exact factorial form. -/
theorem shapePeriod_factorial {p : ℕ} (hp : Odd p) (hp3 : 3 ≤ p) (j : ℕ)
    (haj : alpha p ≤ j) (tau c : ℝ) (ht : 0 < tau) (hc : 0 < c) :
    shapePeriod (p-1) j tau (c : ℂ) =
      (((p.factorial : ℝ)*Real.pi^((p-1)/2)*factorialProduct p / Real.sqrt p) *
        ((j-alpha p).factorial : ℝ)/(c^(alpha p)*tau^(j+1-alpha p)*j.factorial) : ℝ) := by
  have ha : 0 < alpha p := by
    rw [alpha_eq_derivativeOrder]
    exact IsingBulk.HT.First.derivativeOrder_pos hp hp3
  have he : (p-1)-1+((p-1)+1)*(p-1) = 2*alpha p-1 := by
    rw [show p-1+1=p by omega, alpha_eq_derivativeOrder]
    exact IsingBulk.HT.First.odd_shape_radial_exponent hp hp3
  rw [shapePeriod_real_radial (by omega), he, radialBeta_order (alpha p) j ha haj tau c ht hc,
    ← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  have hang := IsingBulk.HT.First.shapeAngularConstant_factorial_identity hp hp3
  rw [← alpha_eq_derivativeOrder, ← factorialProduct_eq_amplitude (by omega)] at hang
  have hs : Real.sqrt (p : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast (show 0<p by omega)))
  have hga : shapeAngularConstant (p-1)*((alpha p-1).factorial : ℝ)/2 =
      (p.factorial : ℝ)*Real.pi^((p-1)/2)*factorialProduct p / Real.sqrt p := by
    apply (eq_div_iff hs).2
    linear_combination hang / 2
  calc
    _ = (shapeAngularConstant (p-1)*((alpha p-1).factorial : ℝ)/2) *
        ((j-alpha p).factorial : ℝ)/(c^(alpha p)*tau^(j+1-alpha p)*j.factorial) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by rw [hga]


open IsingBulk.Anisotropic.NegativeDominance in
/-- Gamma form of the actual period, valid for growing p and j. -/
theorem shapePeriod_gamma {p : ℕ} (hp : Odd p) (hp3 : 3 ≤ p) (j : ℕ)
    (haj : alpha p ≤ j) (tau c : ℝ) (ht : 0 < tau) (hc : 0 < c) :
    shapePeriod (p-1) j tau (c : ℂ) =
      (((p.factorial : ℝ)*Real.pi^((p-1)/2)*factorialProduct p / Real.sqrt p) /
        (c^(alpha p)*tau^(j+1-alpha p)) *
        (Real.Gamma ((j : ℝ)+1-alpha p)/Real.Gamma ((j : ℝ)+1)) : ℝ) := by
  have he : (j : ℝ)+1-alpha p = ((j-alpha p : ℕ) : ℝ)+1 := by
    rw [Nat.cast_sub haj]
    ring
  rw [shapePeriod_factorial hp hp3 j haj tau c ht hc, he,
    Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial]
  apply congrArg Complex.ofReal
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

open IsingBulk.Anisotropic.NegativeDominance in
/-- Equation (4.46), with its exact Gamma quotient and constrained Jacobian.
The nonnegative exponent j+1-α is equivalent to the manuscript's inverse power. -/
theorem negativeEdge_exact_period {p : ℕ} (hp : Odd p) (hp3 : 3 ≤ p) (j : ℕ)
    (haj : alpha p ≤ j) :
    shapePeriod (p-1) j (tau p) ((1/(2*(p : ℝ)) : ℝ) : ℂ) =
      (((p.factorial : ℝ)*Real.pi^((p-1)/2)*factorialProduct p / Real.sqrt p) *
        (2*(p : ℝ))^(alpha p) / (tau p)^(j+1-alpha p) *
        (Real.Gamma ((j : ℝ)+1-alpha p)/Real.Gamma ((j : ℝ)+1)) : ℝ) := by
  rw [shapePeriod_gamma hp hp3 j haj (tau p) (1/(2*(p : ℝ)))
    (tau_pos p (by omega)) (by positivity)]
  apply congrArg Complex.ofReal
  simp [div_eq_mul_inv, mul_inv_rev, mul_pow, mul_assoc, mul_left_comm, mul_comm]


/-- The literal Gaussian integral in the p−1 independent zero-mean coordinates. -/
def constrainedGaussian (p : ℕ) : ℝ :=
  ∫ t : Fin (p-1) → ℝ,
    let x := shapeCoordinateEquiv (p-1) (WithLp.toLp 2 t)
    shapeVandermondeSq x * Real.exp (-‖x‖^2)

open IsingBulk.Anisotropic.NegativeDominance in
/-- Equation (4.45), including the free-coordinate 1/√p Jacobian. -/
theorem constrainedGaussian_exact {p : ℕ} (hp : Odd p) (hp3 : 3 ≤ p) :
    constrainedGaussian p =
      (p.factorial : ℝ)*Real.pi^((p-1)/2)*factorialProduct p / Real.sqrt p := by
  have hN : p-1+1=p := by omega
  have hNR : ((p-1 : ℕ) : ℝ)+1 = (p : ℝ) := by exact_mod_cast hN
  have ha : 1 ≤ IsingBulk.HT.First.derivativeOrder p :=
    IsingBulk.HT.First.derivativeOrder_pos hp hp3
  have he : (p-1)-1+((p-1)+1)*(p-1) = 2*IsingBulk.HT.First.derivativeOrder p-1 := by
    rw [hN]
    exact IsingBulk.HT.First.odd_shape_radial_exponent hp hp3
  have hpolar := integral_shapeVandermonde_polar (show 1 ≤ p-1 by omega)
    (fun r => (Real.exp (-r^2) : ℂ))
  simp only [Complex.real_smul, ← Complex.ofReal_mul, integral_complex_ofReal] at hpolar
  rw [he, IsingBulk.HT.First.integral_odd_gaussian_radial ha] at hpolar
  have hfree := integral_shapeExtend (p-1)
    (fun x => ((shapeVandermondeSq x * Real.exp (-‖x‖^2) : ℝ) : ℂ))
  simp only [integral_complex_ofReal, hNR] at hfree
  change (constrainedGaussian p : ℂ) = _ at hfree
  rw [hpolar] at hfree
  have hang := IsingBulk.HT.First.shapeAngularConstant_factorial_identity hp hp3
  rw [← factorialProduct_eq_amplitude (by omega)] at hang
  unfold shapeAngularConstant at hang
  rw [hNR] at hang
  have hs : Real.sqrt (p : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast (show 0<p by omega)))
  apply Complex.ofReal_injective
  rw [hfree]
  simp only [Complex.real_smul, ← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  apply (eq_div_iff hs).2
  linear_combination hang / 2

end
end IsingBulk.Anisotropic.NegativeNormalForm
