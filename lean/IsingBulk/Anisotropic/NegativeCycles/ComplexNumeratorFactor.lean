import IsingBulk.Anisotropic.NegativeCycles.LocalPairContraction
import IsingBulk.Anisotropic.NegativeDominance.OddIndices

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.First IsingBulk.Anisotropic.NegativeNormalForm
open IsingBulk.Anisotropic.NegativeDominance
open scoped BigOperators

theorem alpha_eq_pairs_add (m : ℕ) : alpha (2*m+1)=(2*m+1).choose 2+m := by
  rw [alpha_two_mul_add_one,Nat.choose_two_right]
  have h : (2*m+1)*(2*m+1-1)=2*(m*(2*m+1)) := by
    rw [Nat.add_sub_cancel]
    ring
  rw [h,Nat.mul_div_cancel_left _ (by norm_num : 0<2)]
  ring

/-- All quadratic-in-N powers of B are absorbed into actual small complete
pair factors, leaving only the linear power B^m. -/
theorem formFactorNumerator_odd_complete_pairs (m : ℕ) (B rootB : ℂ→ℂ)
    (phi : ℝ) (hphi : Real.sin phi≠0) (d t : ℂ) (v : Config (2*m+1)) :
    formFactorNumerator B rootB phi hphi d t v=
      (rootB t*B t^m / (((2*m+1).factorial:ℂ)*(2*(Real.pi:ℂ))^(2*m))) *
      (∏ i, (Complex.sinh (negativePhase B phi hphi t (d+v i)))⁻¹) *
      ∏ p∈firstStrictPairs (2*m+1),localCompletePair B phi hphi t (d+v p.1) (d+v p.2) := by
  have hp : (∏ p∈firstStrictPairs (2*m+1),
      localCompletePair B phi hphi t (d+v p.1) (d+v p.2))=
      B t^((2*m+1).choose 2) *
      ∏ p∈firstStrictPairs (2*m+1),
        (Complex.sin ((v p.1-v p.2)/2)/pairDenominator B phi hphi d t (v p.1) (v p.2))^2 := by
    simp [localCompletePair,pairDenominator,Finset.prod_mul_distrib,firstStrictPairs_card]
  rw [hp,formFactorNumerator,densityPrefactor,alpha_eq_pairs_add,pow_add]
  simp only [Nat.add_sub_cancel]
  ring

end IsingBulk.Anisotropic.NegativeCycles
