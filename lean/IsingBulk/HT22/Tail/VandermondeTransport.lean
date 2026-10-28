import IsingBulk.HT22.Tail.PairFactorization
import IsingBulk.Preferred22.VandermondeTransport

/-! # Collision filtration of the new mixed field

The complete Vandermonde survives the material derivative. Its singular
scale cost occurs in the actual field coefficient, not by a claim that
partial collision denominators are bounded away from zero.
-/
namespace IsingBulk.HT22.Tail
noncomputable section
open IsingBulk.Preferred22 IsingBulk.HT22.Geometry
open scoped BigOperators

/-- Actual divided-difference coefficient of the fixed-v mixed field. -/
def residualPairSlope {N : ℕ} (t : ℂ) (v : Fin N → ℂ) (i j : Fin N) : ℂ :=
  (-(∑ a, inverseT t (v a)))/sourceCovariance t v * (N:ℂ) *
    dslope (regularInverse t) (v j) (v i)

/-- A genuine algebraic identity valid also on every partial diagonal.
The dslope is analytic when the inverse is, rather than a punctured quotient. -/
theorem residualField_difference {N : ℕ} (t : ℂ) (v : Fin N → ℂ) (i j : Fin N) :
    residualField t v i-residualField t v j=(v i-v j)*residualPairSlope t v i j := by
  have hG : centeredAngleSum (fun a => regularInverse t (v a)) i-
      centeredAngleSum (fun a => regularInverse t (v a)) j=
      (N:ℂ)*(regularInverse t (v i)-regularInverse t (v j)) := by
    unfold centeredAngleSum
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    ring
  have hd : (v i-v j)*dslope (regularInverse t) (v j) (v i)=
      regularInverse t (v i)-regularInverse t (v j) := by
    simpa only [smul_eq_mul] using sub_smul_dslope (regularInverse t) (v j) (v i)
  change (-(∑ a,inverseT t (v a)))/sourceCovariance t v *
      centeredAngleSum (fun a=>regularInverse t (v a)) i-
    (-(∑ a,inverseT t (v a)))/sourceCovariance t v *
      centeredAngleSum (fun a=>regularInverse t (v a)) j=_
  rw [←mul_sub,hG,←hd]
  unfold residualPairSlope
  ring

/-- The new field transports the full N(N−1)-degree collision product.
Quantitative bounds on the displayed real source coefficient are separate. -/
theorem squaredVandermonde_residual_directional {N : ℕ} (t : ℂ) (v : Fin N → ℂ) :
    fderiv ℂ squaredVandermonde v (residualField t v)=
      2*(∑ i, ∑ j∈Finset.Ioi i, residualPairSlope t v i j)*squaredVandermonde v := by
  change fderiv ℂ preferredSquaredVandermonde v (residualField t v)=_
  exact preferredSquaredVandermonde_directional v (residualField t v)
    (residualPairSlope t v) (residualField_difference t v)

end
end IsingBulk.HT22.Tail
