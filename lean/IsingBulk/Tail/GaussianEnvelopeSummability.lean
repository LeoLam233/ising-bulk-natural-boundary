import IsingBulk.Tail.NatExponentialEnvelope
import IsingBulk.Tail.AllBranchNumeratorGaussian

namespace IsingBulk.Tail
noncomputable section
open Filter

theorem linear_envelope_numerator_gaussian_summable {f : ℕ → ℝ}
    (hf : NatExponentialEnvelope 1 f) (j : ℕ) (A : ℝ) (hA : 1 ≤ A) :
    Summable (fun N => f N*allBranchNumeratorJetBudget N j A) := by
  obtain ⟨C,hC,hf⟩ := hf
  obtain ⟨D,_,hgauss⟩ := allBranchNumeratorJetBudget_gaussian j A hA
  have hk : 0 < Real.log 2/2 := by positivity
  apply (summable_polynomial_gaussian (C+D) hk (2*j)).of_norm_bounded_eventually
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop (2:ℕ)] with N hN
  have hnum : 0 ≤ allBranchNumeratorJetBudget N j A := by unfold allBranchNumeratorJetBudget; positivity
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hnum]
  calc
    _ ≤ Real.exp (C*(N:ℝ))*((N:ℝ)^(2*j)*Real.exp (D*N-(Real.log 2/2)*(N:ℝ)^2)) := by
      apply mul_le_mul _ (hgauss N hN) hnum (Real.exp_nonneg _)
      simpa only [pow_one] using hf N (by omega)
    _ = _ := by rw [← mul_assoc,mul_comm _ ((N:ℝ)^(2*j)),mul_assoc,← Real.exp_add]; congr 2; ring

end
end IsingBulk.Tail
