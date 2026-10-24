import IsingBulk.Anisotropic.NegativeNormalForm.ComplexBetaPrimitive
import Mathlib.Analysis.Complex.RealDeriv

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open Polynomial MeasureTheory Set

def complexCompactBetaIntegrand (m k : ℕ) (h : ℂ) (x : ℝ) : ℂ :=
  (x:ℂ)^m*(1-(x:ℂ))^k/(1+(h-1)*(x:ℂ))^(m+k+2)

theorem complexCompactBetaIntegrand_continuousOn (m k : ℕ) (h : ℂ) (hh : 0<h.re) :
    ContinuousOn (complexCompactBetaIntegrand m k h) (Icc (0:ℝ) 1) := by
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro x hx
    exact pow_ne_zero _ (complexBetaMobius_den_ne h hh hx)

theorem betaPrimitive_mobius_derivative (m k : ℕ) (h : ℂ) (P : Polynomial ℂ)
    (hP : P.derivative=Polynomial.X^m*(1-Polynomial.X)^k) (z : ℂ)
    (hz : 1+(h-1)*z≠0) :
    HasDerivAt (fun z => P.eval (complexBetaMobius h z))
      (h^(m+1)*(z^m*(1-z)^k/(1+(h-1)*z)^(m+k+2))) z := by
  have hd := (P.hasDerivAt (complexBetaMobius h z)).comp z (complexBetaMobius_hasDerivAt h z hz)
  rw [hP] at hd
  simp only [Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_sub,
    Polynomial.eval_one] at hd
  convert hd using 1
  · rfl
  · have he : 1-complexBetaMobius h z=(1-z)/(1+(h-1)*z) := by
      dsimp [complexBetaMobius]
      apply (eq_div_iff hz).2
      rw [sub_mul,one_mul,div_mul_cancel₀ _ hz]
      ring
    rw [he]
    dsimp [complexBetaMobius]
    simp only [div_pow,mul_pow,pow_add,pow_succ]
    field_simp [hz]

/-- The complete complex beta deformation is exact on the right half-plane.
This is proved by a polynomial primitive along the actual complex Möbius
curve, not by assuming contour equality or a complex period formula. -/
theorem complexCompactBeta_factorial (m k : ℕ) (h : ℂ) (hh : 0<h.re) :
    (∫ x in (0:ℝ)..1, complexCompactBetaIntegrand m k h x)=
      ((m.factorial:ℂ)*k.factorial/(m+k+1).factorial)/h^(m+1) := by
  obtain ⟨P,hP⟩ := polynomial_exists_primitive (Polynomial.X^m*(1-Polynomial.X)^k)
  have hn : h≠0 := by intro he; simp [he] at hh
  have hc := complexCompactBetaIntegrand_continuousOn m k h hh
  have hd (x : ℝ) (hx : x∈uIcc (0:ℝ) 1) :
      HasDerivAt (fun x : ℝ => P.eval (complexBetaMobius h x))
        (h^(m+1)*complexCompactBetaIntegrand m k h x) x := by
    apply (betaPrimitive_mobius_derivative m k h P hP (x:ℂ) ?_).comp_ofReal
    exact complexBetaMobius_den_ne h hh (by simpa using hx)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((continuousOn_const.mul hc).intervalIntegrable_of_Icc (by norm_num : (0:ℝ)≤1))
  rw [intervalIntegral.integral_const_mul] at hi
  simp only [Complex.ofReal_one,Complex.ofReal_zero,complexBetaMobius,mul_zero,
    add_zero,zero_div,mul_one,add_sub_cancel,div_self hn] at hi
  have hd1 (x : ℝ) (_hx : x∈uIcc (0:ℝ) 1) :
      HasDerivAt (fun x : ℝ => P.eval (x:ℂ)) ((x:ℂ)^m*(1-(x:ℂ))^k) x := by
    have hd := (P.hasDerivAt (x:ℂ)).comp_ofReal
    simpa [hP] using hd
  have hi1 := intervalIntegral.integral_eq_sub_of_hasDerivAt hd1
    (by apply Continuous.intervalIntegrable; fun_prop)
  simp only [Complex.ofReal_one,Complex.ofReal_zero] at hi1
  have hreal : (∫ x in (0:ℝ)..1, (x:ℂ)^m*(1-(x:ℂ))^k)=
      (m.factorial:ℂ)*k.factorial/(m+k+1).factorial := by
    have hh := congrArg Complex.ofReal (compactBeta_factorial m k)
    rw [←intervalIntegral.integral_ofReal] at hh
    simpa only [Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_sub,
      Complex.ofReal_one,Complex.ofReal_div,Complex.ofReal_natCast] using hh
  rw [hreal] at hi1
  rw [←hi1] at hi
  exact (eq_div_iff (pow_ne_zero _ hn)).2 (by simpa [mul_comm] using hi)

end
end IsingBulk.Anisotropic.NegativeNormalForm
