import IsingBulk.Algebra.SchurPfaffian
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.MvPolynomial.Eval

/-! Exact rational-function statement for all even sizes, with genuine nonzero
generic denominators. `SchurMobius.rationalIdentity` proves this statement;
`SchurContinuation` proves its pole-free complex specialization. -/

namespace IsingBulk.Schur

abbrev RationalField (n : ℕ) := FractionRing (MvPolynomial (Fin (2*n)) ℚ)

noncomputable def genericVariable (n : ℕ) (i : Fin (2*n)) : RationalField n :=
  algebraMap (MvPolynomial (Fin (2*n)) ℚ) (RationalField n) (MvPolynomial.X i)

/-- The generic pair denominators are genuine nonzero rational functions,
including when the two indices coincide. -/
theorem generic_denominator_ne_zero (n : ℕ) (i j : Fin (2*n)) :
    1-genericVariable n i * genericVariable n j ≠ 0 := by
  have hp : (1-MvPolynomial.X i * MvPolynomial.X j : MvPolynomial (Fin (2*n)) ℚ) ≠ 0 := by
    intro h
    have he := congrArg (MvPolynomial.eval (fun _ => (0 : ℚ))) h
    norm_num at he
  have hm := (IsFractionRing.injective (MvPolynomial (Fin (2*n)) ℚ) (RationalField n)).ne hp
  simpa only [map_sub, map_one, map_mul, map_zero, genericVariable] using hm

/-- General even-N Schur identity in a fraction field; proved by `rationalIdentity`.
This definition itself is a proposition specification. -/
def RationalIdentity (n : ℕ) : Prop :=
  let v := List.ofFn (genericVariable n)
  pfaffian (fun x y => (x-y)/(1-x*y)) n v =
    pairProduct (fun x y => (x-y)/(1-x*y)) v

end IsingBulk.Schur
