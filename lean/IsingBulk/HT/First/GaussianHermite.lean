import Mathlib.RingTheory.Polynomial.Hermite.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-! Unnormalized probabilists' Hermite orthogonality for the literal
Gaussian weight exp(-x²/2). No integral normalization is assumed. -/
namespace IsingBulk.HT.First.Gaussian
noncomputable section
open MeasureTheory Polynomial
open scoped Polynomial

/-- The manuscript uses unnormalized Lebesgue Gaussian weight. -/
def gaussianWeight (x : ℝ) : ℝ := Real.exp (-(x^2/2))

/-- The pinned mathlib Hermite polynomials are defined over the integers. -/
def realHermite (m : ℕ) : ℝ[X] :=
  (Polynomial.hermite m).map (Int.castRingHom ℝ)

@[simp] theorem realHermite_zero : realHermite 0 = 1 := by
  simp [realHermite]

@[simp] theorem realHermite_succ (m : ℕ) :
    realHermite (m+1) = X*realHermite m-(realHermite m).derivative := by
  simp [realHermite,Polynomial.hermite_succ,Polynomial.derivative_map]

theorem realHermite_monic (m : ℕ) : (realHermite m).Monic :=
  (Polynomial.hermite_monic m).map _

theorem realHermite_natDegree (m : ℕ) : (realHermite m).natDegree = m := by
  rw [realHermite,(Polynomial.hermite_monic m).natDegree_map,Polynomial.natDegree_hermite]

theorem polynomial_gaussian_integrable (P : ℝ[X]) :
    Integrable (fun x : ℝ => P.eval x*gaussianWeight x) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
      have hh := hP.add hQ
      convert! hh using 1
      all_goals simp only [Polynomial.eval_add, add_mul]
      all_goals rfl
  | monomial n c =>
      have h := integrable_rpow_mul_exp_neg_mul_sq
        (b := (1/2:ℝ)) (s := (n:ℝ)) (by norm_num)
        (lt_of_lt_of_le (by norm_num : (-1:ℝ) < 0) (Nat.cast_nonneg n))
      have he : (fun x : ℝ => x^n*gaussianWeight x) =
          (fun x : ℝ => x^(n:ℝ)*Real.exp (-(1/2:ℝ)*x^2)) := by
        funext x
        rw [Real.rpow_natCast]
        congr 1
        unfold gaussianWeight
        congr 1
        ring
      rw [← he] at h
      simpa only [Polynomial.eval_monomial,mul_assoc] using h.const_mul c

theorem polynomial_pair_gaussian_integrable (P Q : ℝ[X]) :
    Integrable (fun x : ℝ => P.eval x*Q.eval x*gaussianWeight x) := by
  simpa only [Polynomial.eval_mul] using polynomial_gaussian_integrable (P*Q)

theorem gaussianWeight_hasDerivAt (x : ℝ) :
    HasDerivAt gaussianWeight (-x*gaussianWeight x) x := by
  change HasDerivAt (fun y : ℝ => Real.exp (-(y^2/2)))
    (-x*Real.exp (-(x^2/2))) x
  have hh := (((hasDerivAt_id x).pow 2).div_const 2).neg.exp
  convert! hh using 1
  all_goals simp
  all_goals ring

/-- Integration by parts is justified by polynomial-Gaussian integrability
on the whole real line, with no unproved boundary-decay premise. -/
theorem gaussian_polynomial_derivative_integral (P : ℝ[X]) :
    (∫ x : ℝ, P.derivative.eval x*gaussianWeight x) =
      ∫ x : ℝ, (X*P).eval x*gaussianWeight x := by
  have hv : Integrable ((fun x : ℝ => P.eval x)*
      (fun x : ℝ => -x*gaussianWeight x)) := by
    convert polynomial_gaussian_integrable (-X*P) using 1
    funext x
    simp only [Pi.mul_apply,Polynomial.eval_mul,Polynomial.eval_neg,Polynomial.eval_X]
    ring
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x : ℝ => P.eval x) (v := gaussianWeight)
    (u' := fun x : ℝ => P.derivative.eval x)
    (v' := fun x : ℝ => -x*gaussianWeight x)
    (fun x _ => P.hasDerivAt x) (fun x _ => gaussianWeight_hasDerivAt x)
    hv (polynomial_gaussian_integrable P.derivative) (polynomial_gaussian_integrable P)
  have he : (fun x : ℝ => P.eval x*(-x*gaussianWeight x)) =
      (fun x : ℝ => -((X*P).eval x*gaussianWeight x)) := by
    funext x
    simp only [Polynomial.eval_mul,Polynomial.eval_X]
    ring
  rw [he,integral_neg] at h
  exact (neg_inj.mp h).symm

/-- Gaussian adjoint: multiplication by x minus differentiation is adjoint
to differentiation for this exact, unnormalized weight. -/
theorem gaussian_polynomial_adjoint (P Q : ℝ[X]) :
    (∫ x : ℝ, (X*P-P.derivative).eval x*Q.eval x*gaussianWeight x) =
      ∫ x : ℝ, P.eval x*Q.derivative.eval x*gaussianWeight x := by
  have h := gaussian_polynomial_derivative_integral (P*Q)
  have hleft : (∫ x : ℝ, (P*Q).derivative.eval x*gaussianWeight x) =
      (∫ x : ℝ, P.derivative.eval x*Q.eval x*gaussianWeight x)+
      ∫ x : ℝ, P.eval x*Q.derivative.eval x*gaussianWeight x := by
    simp only [Polynomial.derivative_mul,Polynomial.eval_add,Polynomial.eval_mul,add_mul]
    exact integral_add (polynomial_pair_gaussian_integrable P.derivative Q)
      (polynomial_pair_gaussian_integrable P Q.derivative)
  have hright : (∫ x : ℝ, (X*(P*Q)).eval x*gaussianWeight x) =
      ∫ x : ℝ, (X*P).eval x*Q.eval x*gaussianWeight x := by
    congr 1
    funext x
    simp only [Polynomial.eval_mul,Polynomial.eval_X]
    ring
  rw [hleft,hright] at h
  calc
    _ = (∫ x : ℝ, (X*P).eval x*Q.eval x*gaussianWeight x)-
        ∫ x : ℝ, P.derivative.eval x*Q.eval x*gaussianWeight x := by
      simp only [Polynomial.eval_sub,sub_mul]
      exact integral_sub (polynomial_pair_gaussian_integrable (X*P) Q)
        (polynomial_pair_gaussian_integrable P.derivative Q)
    _ = _ := by linarith

/-- Universal Hermite pairing, proved by the polynomial recurrence and the
justified Gaussian adjoint identity. -/
theorem hermite_gaussian_pairing (m : ℕ) (P : ℝ[X]) :
    (∫ x : ℝ, (realHermite m).eval x*P.eval x*gaussianWeight x) =
      ∫ x : ℝ, (Polynomial.derivative^[m] P).eval x*gaussianWeight x := by
  induction m generalizing P with
  | zero => simp only [realHermite_zero,Polynomial.eval_one,one_mul,Function.iterate_zero_apply]
  | succ m ih =>
      rw [realHermite_succ,gaussian_polynomial_adjoint,ih]
      rw [Function.iterate_succ_apply]

theorem realHermite_top_derivative (m : ℕ) :
    Polynomial.derivative^[m] (realHermite m) = Polynomial.C (m.factorial:ℝ) := by
  have hd : (Polynomial.derivative^[m] (realHermite m)).natDegree = 0 := by
    apply Nat.eq_zero_of_le_zero
    have h := Polynomial.natDegree_iterate_derivative (realHermite m) m
    simpa only [realHermite_natDegree,Nat.sub_self] using h
  rw [Polynomial.eq_C_of_natDegree_eq_zero hd]
  congr 1
  rw [Polynomial.coeff_iterate_derivative,zero_add]
  have hc : (realHermite m).coeff m = 1 := by
    simpa only [realHermite_natDegree] using (realHermite_monic m).coeff_natDegree
  rw [hc,Nat.descFactorial_self,nsmul_eq_mul,mul_one]

theorem gaussianWeight_integral :
    (∫ x : ℝ, gaussianWeight x) = Real.sqrt (2*Real.pi) := by
  have he : gaussianWeight = (fun x : ℝ => Real.exp (-(1/2:ℝ)*x^2)) := by
    funext x
    unfold gaussianWeight
    congr 1
    ring
  rw [he,integral_gaussian]
  congr 1
  ring

theorem hermite_gaussian_integrable (m l : ℕ) :
    Integrable (fun x : ℝ => (realHermite m).eval x*(realHermite l).eval x*gaussianWeight x) :=
  polynomial_pair_gaussian_integrable _ _

/-- Exact squared norms and orthogonality for probabilists' monic Hermite
polynomials under the manuscript's Lebesgue Gaussian weight. -/
theorem hermite_gaussian_inner (m l : ℕ) :
    (∫ x : ℝ, (realHermite m).eval x*(realHermite l).eval x*gaussianWeight x) =
      if m=l then Real.sqrt (2*Real.pi)*(m.factorial:ℝ) else 0 := by
  rcases lt_trichotomy m l with hml | rfl | hlm
  · rw [ite_eq_right hml.ne]
    have he : (fun x : ℝ => (realHermite m).eval x*(realHermite l).eval x*gaussianWeight x) =
        (fun x : ℝ => (realHermite l).eval x*(realHermite m).eval x*gaussianWeight x) := by
      funext x
      ring
    rw [he,hermite_gaussian_pairing]
    rw [Polynomial.iterate_derivative_eq_zero (by simpa only [realHermite_natDegree] using hml)]
    simp only [Polynomial.eval_zero,zero_mul,integral_zero]
  · rw [ite_eq_left rfl,hermite_gaussian_pairing,realHermite_top_derivative]
    simp only [Polynomial.eval_C,integral_const_mul,gaussianWeight_integral]
    ring
  · rw [ite_eq_right hlm.ne']
    rw [hermite_gaussian_pairing,
      Polynomial.iterate_derivative_eq_zero (by simpa only [realHermite_natDegree] using hlm)]
    simp only [Polynomial.eval_zero,zero_mul,integral_zero]

end
end IsingBulk.HT.First.Gaussian
