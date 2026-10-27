import IsingBulk.Preferred22.MarkedMinorBound
import IsingBulk.Preferred22.NormalConvergence

/-! The actual factorial normalization of a marked complementary minor
retains the summable `N^(-N/2)` determinant decay. -/
namespace IsingBulk.Preferred22
noncomputable section
open scoped Matrix.Norms.Elementwise

theorem markedDeterminant_factorial_bound {N ell : ℕ} (hN : 0<N)
    (K : Matrix (Fin N) (Fin N) ℂ) (marks : Fin ell → Fin N × Fin N)
    (a : ℝ) (ha : 0<a) (hK : ∀ i j, ‖K i j‖ ≤ a) :
    ‖markedDeterminant K marks‖/(N.factorial:ℝ) ≤
      (Real.exp 1/Real.sqrt N)^N * a^(N-ell) := by
  have hf : (0:ℝ)<N.factorial := by exact_mod_cast Nat.factorial_pos N
  calc
    _ ≤ ((Real.sqrt N)^N*a^(N-ell))/(N.factorial:ℝ) :=
      div_le_div_of_nonneg_right (markedDeterminant_hadamard hN K marks a ha hK) hf.le
    _ = ((Real.sqrt N)^N/(N.factorial:ℝ))*a^(N-ell) := by ring
    _ ≤ (Real.exp 1/Real.sqrt N)^N*a^(N-ell) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      simpa only [mul_one] using sqrt_factorial_envelope hN (B := 1) (by norm_num)

end
end IsingBulk.Preferred22
