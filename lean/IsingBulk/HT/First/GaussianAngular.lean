import IsingBulk.HT.First.IntrinsicGaussian
import IsingBulk.HT.First.ClosedAmplitude
import IsingBulk.First.ShapePolar
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Algebra.BigOperators.Intervals

/-! Exact angular Vandermonde normalization from the actual intrinsic
Gaussian integral and the odd radial Gamma integral. The free-coordinate
Jacobian 1/sqrt(p) is retained explicitly. -/
namespace IsingBulk.HT.First
noncomputable section
open MeasureTheory Set IsingBulk.First
open scoped BigOperators

 theorem integral_odd_gaussian_radial {k : ℕ} (hk : 1 ≤ k) :
    (∫ r : ℝ in Ioi 0, r^(2*k-1)*Real.exp (-r^2)) =
      ((k-1).factorial:ℝ)/2 := by
  have hcast : ((k-1:ℕ):ℝ)+1=(k:ℝ) := by exact_mod_cast Nat.sub_add_cancel hk
  have hGamma : Real.Gamma (k:ℝ)=((k-1).factorial:ℝ) := by
    simpa only [hcast] using Real.Gamma_nat_eq_factorial (k-1)
  have hexp : ((2*k-1:ℕ):ℝ)+1=2*(k:ℝ) := by
    exact_mod_cast (show 2*k-1+1=2*k by omega)
  have hquot : (((2*k-1:ℕ):ℝ)+1)/2=(k:ℝ) := by linarith
  have hrad := integral_rpow_mul_exp_neg_rpow
    (p := (2:ℝ)) (q := ((2*k-1:ℕ):ℝ)) (by norm_num)
    (lt_of_lt_of_le (by norm_num : (-1:ℝ)<0) (Nat.cast_nonneg _))
  simp only [Real.rpow_natCast, Real.rpow_two, hquot, hGamma] at hrad
  convert! hrad using 1
  all_goals first | rfl | ring

/-- The half-Gaussian normalization used by the Hermite determinant proof. -/
theorem integral_odd_half_gaussian_radial {k : ℕ} (hk : 1 ≤ k) :
    (∫ r : ℝ in Ioi 0, r^(2*k-1)*Real.exp (-r^2/2)) =
      (2:ℝ)^(k-1)*((k-1).factorial:ℝ) := by
  have hsqrt : (Real.sqrt (2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hpoint (r : ℝ) :
      (Real.sqrt 2*r)^(2*k-1)*Real.exp (-(Real.sqrt 2*r)^2/2) =
      (Real.sqrt 2)^(2*k-1)*(r^(2*k-1)*Real.exp (-r^2)) := by
    rw [mul_pow, mul_pow, hsqrt, show -(2*r^2)/2 = -r^2 by ring]
    ring
  have h := integral_comp_mul_left_Ioi'
    (fun r : ℝ => r^(2*k-1)*Real.exp (-r^2/2)) 0
    (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2))
  simp only [mul_zero] at h
  rw [← h]
  simp_rw [hpoint]
  rw [integral_const_mul, integral_odd_gaussian_radial hk]
  change Real.sqrt 2*((Real.sqrt 2)^(2*k-1)*(((k-1).factorial:ℝ)/2)) = _
  have hpow : Real.sqrt 2*(Real.sqrt 2)^(2*k-1)=(2:ℝ)^k := by
    rw [← pow_succ', show 2*k-1+1=2*k by omega, pow_mul, hsqrt]
  rw [← mul_assoc, hpow]
  have hks : k-1+1=k := Nat.sub_add_cancel hk
  have htwopow : (2:ℝ)^k=(2:ℝ)^(k-1)*2 := by
    calc
      _ = (2:ℝ)^(k-1+1) := congrArg ((2:ℝ)^·) hks.symm
      _ = _ := pow_succ _ _
  rw [htwopow]
  ring

/-- Polar decomposition of the literal intrinsic half-Gaussian integral. -/
theorem intrinsic_gaussian_shape_eq_sphere {p : ℕ} (hp : Odd p) (hp3 : 3 ≤ p) :
    (∫ x : ShapeSpace (p-1), shapeVandermondeSq x*Real.exp (-‖x‖^2/2)) =
      shapeSphereIntegral (p-1)*(2:ℝ)^(derivativeOrder p-1)*
        ((derivativeOrder p-1).factorial:ℝ) := by
  have hk : 1 ≤ derivativeOrder p := derivativeOrder_pos hp hp3
  have hdegree : (p-1)-1+((p-1)+1)*(p-1) = 2*derivativeOrder p-1 := by
    rw [show p-1+1=p by omega]
    exact odd_shape_radial_exponent hp hp3
  have hpolar := integral_shapeVandermonde_polar
    (show 1 ≤ p-1 by omega) (fun r => (Real.exp (-r^2/2):ℂ))
  rw [hdegree] at hpolar
  simp only [Complex.real_smul, ← Complex.ofReal_mul, _root_.integral_complex_ofReal] at hpolar
  rw [integral_odd_half_gaussian_radial hk] at hpolar
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_mul, mul_assoc] using hpolar

/-- Convert the written product over 1,...,p-1 to the exact Hermite norms. -/
theorem factorialAmplitudeProduct_eq_fin {p : ℕ} (hp : 1 ≤ p) :
    factorialAmplitudeProduct p =
      (∏ i : Fin p, (i.val.factorial:ℝ))/(2:ℝ)^(p.choose 2) := by
  have hN : p-1+1=p := by omega
  have hinterval : Finset.Icc 1 (p-1)=Finset.Ico 1 p := by
    rw [← Finset.Ico_add_one_right_eq_Icc, hN]
  have hprod : factorialAmplitudeProduct p =
      ∏ m ∈ Finset.range p, (m.factorial:ℝ)/(2:ℝ)^m := by
    rw [factorialAmplitudeProduct, hinterval]
    symm
    simpa using Finset.prod_range_eq_mul_Ico
      (fun m : ℕ => (m.factorial:ℝ)/(2:ℝ)^m) (show 0<p by omega)
  have hsum : (∑ m ∈ Finset.range p, m)=p.choose 2 := by
    rw [Finset.sum_range_id, Nat.choose_two_right]
  rw [hprod, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, hsum]
  exact congrArg (fun x : ℝ => x/(2:ℝ)^(p.choose 2))
    (Fin.prod_univ_eq_prod_range (fun m : ℕ => (m.factorial:ℝ)) p).symm

/-- Exact multiplied angular identity, with all factorial and Jacobian factors. -/
theorem shapeAngularConstant_factorial_identity {p : ℕ} (hp : Odd p) (hp3 : 3 ≤ p) :
    shapeAngularConstant (p-1)*((derivativeOrder p-1).factorial:ℝ)*Real.sqrt p =
      2*(p.factorial:ℝ)*Real.pi^((p-1)/2)*factorialAmplitudeProduct p := by
  have hN : p-1+1=p := by omega
  have hNR : ((p-1:ℕ):ℝ)+1=(p:ℝ) := by exact_mod_cast hN
  have hpR : (0:ℝ)<p := by exact_mod_cast (show 0<p by omega)
  have hshape := intrinsic_gaussian_shape_integral (p-1)
  rw [intrinsic_gaussian_shape_eq_sphere hp hp3] at hshape
  rw [hN] at hshape
  have hfac : (∏ m ∈ Finset.Icc 1 p, (m.factorial:ℝ)) =
      (p.factorial:ℝ)*∏ i : Fin p, (i.val.factorial:ℝ) := by
    have hprod : (∏ i : Fin p, (i.val.factorial:ℝ)) =
        ∏ m ∈ Finset.range p, (m.factorial:ℝ) :=
      Fin.prod_univ_eq_prod_range (fun m : ℕ => (m.factorial:ℝ)) p
    rw [hprod]
    have hnat : (∏ m ∈ Finset.Icc 1 p, m.factorial) =
        p.factorial*∏ m ∈ Finset.range p, m.factorial := by
      rw [Nat.prod_Icc_factorial, ← Nat.prod_range_succ_factorial, Finset.prod_range_succ]
      ring
    exact_mod_cast hnat
  have hpow : Real.sqrt (2*Real.pi)^(p-1) =
      (2:ℝ)^((p-1)/2)*Real.pi^((p-1)/2) := by
    have he : p-1=2*((p-1)/2) := by obtain ⟨m,hm⟩ := hp; omega
    calc
      _ = Real.sqrt (2*Real.pi)^(2*((p-1)/2)) := congrArg (Real.sqrt (2*Real.pi)^·) he
      _ = _ := by rw [pow_mul, Real.sq_sqrt (by positivity), mul_pow]
  have hexp : derivativeOrder p = p.choose 2+(p-1)/2 := by
    have htwice := firstStrictPairs_twice_card (p-1)
    rw [hN, firstStrictPairs_card] at htwice
    have he : p-1=2*((p-1)/2) := by obtain ⟨m,hm⟩ := hp; omega
    have ho := odd_square_order hp
    have hpole : p*(p-1)+p=p^2 := by nlinarith
    omega
  have hk := derivativeOrder_pos hp hp3
  have hks : derivativeOrder p-1+1=derivativeOrder p := by omega
  have hscale : (2:ℝ)^((p-1)/2)*(2:ℝ)^(p.choose 2) =
      2*(2:ℝ)^(derivativeOrder p-1) := by
    calc
      _ = (2:ℝ)^(derivativeOrder p) := by rw [← pow_add, Nat.add_comm, ← hexp]
      _ = (2:ℝ)^(derivativeOrder p-1+1) := congrArg ((2:ℝ)^·) hks.symm
      _ = _ := by rw [pow_succ]; ring
  have hprod : (∏ i : Fin p, (i.val.factorial:ℝ)) =
      factorialAmplitudeProduct p*(2:ℝ)^(p.choose 2) := by
    rw [factorialAmplitudeProduct_eq_fin (by omega)]
    symm
    exact div_mul_cancel₀ _ (pow_ne_zero _ (by norm_num : (2:ℝ) ≠ 0))
  rw [hfac, hpow, hprod] at hshape
  have hscalar : shapeSphereIntegral (p-1)*((derivativeOrder p-1).factorial:ℝ) =
      2*(p.factorial:ℝ)*Real.pi^((p-1)/2)*factorialAmplitudeProduct p := by
    apply mul_right_cancel₀ (pow_ne_zero (derivativeOrder p-1) (by norm_num : (2:ℝ)≠0))
    calc
      _ = shapeSphereIntegral (p-1)*(2:ℝ)^(derivativeOrder p-1)*
          ((derivativeOrder p-1).factorial:ℝ) := by ring
      _ = _ := hshape
      _ = _ := by
        calc
          _ = ((2:ℝ)^((p-1)/2)*(2:ℝ)^(p.choose 2))*
              ((p.factorial:ℝ)*Real.pi^((p-1)/2)*factorialAmplitudeProduct p) := by ring
          _ = _ := by rw [hscale]; ring
  unfold shapeAngularConstant
  rw [hNR]
  calc
    _ = ((Real.sqrt (p:ℝ))⁻¹*Real.sqrt p)*
        (shapeSphereIntegral (p-1)*((derivativeOrder p-1).factorial:ℝ)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ (Real.sqrt_pos.mpr hpR).ne', one_mul, hscalar]

end
end IsingBulk.HT.First
