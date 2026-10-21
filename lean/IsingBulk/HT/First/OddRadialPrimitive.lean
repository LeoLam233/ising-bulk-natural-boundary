import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Convert

/-!
HT-1.0 first-coefficient radial primitive. This is the exact integer-power
identity used in place of the LT half-integer beta integral. It remains valid
for either nonzero sign of the curvature. The improper integral and its
identification with the actual localized contour are separate obligations.
-/
namespace IsingBulk.HT.First
noncomputable section

/-- Integer-power primitive of the HT odd radial quotient. -/
theorem odd_radial_primitive_hasDerivAt (m : ℕ) (Q c x : ℂ)
    (hden : Q+c*x ≠ 0) :
    HasDerivAt (fun z : ℂ => (c*z/(Q+c*z))^(m+1))
      (((m+1:ℕ):ℂ)*Q*c^(m+1)*x^m/(Q+c*x)^(m+2)) x := by
  have hlinear : HasDerivAt (fun z : ℂ => c*z) c x := by
    simpa using (hasDerivAt_id x).const_mul c
  have hsum : HasDerivAt (fun z : ℂ => Q+c*z) c x := hlinear.const_add Q
  have hquot := hlinear.div hsum hden
  have h := hquot.pow (m+1)
  convert h using 1
  simp only [Pi.div_apply,Nat.add_sub_cancel,div_pow,mul_pow,pow_succ]
  field_simp
  ring

/-- The manuscript primitive has endpoint value zero at x=0. -/
theorem odd_radial_primitive_zero (m : ℕ) (Q c : ℂ) :
    (c*0/(Q+c*0))^(m+1) = 0 := by simp

/-- Purely imaginary curvature cannot create a pole on the real radial axis
when Q is positive, on either sign of the curvature. -/
theorem odd_radial_denominator_ne_zero {Q : ℝ} (hQ : 0 < Q) (d x : ℝ) :
    (Q:ℂ)-Complex.I*(d:ℂ)*(x:ℂ) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp at hre
  linarith

end
end IsingBulk.HT.First
