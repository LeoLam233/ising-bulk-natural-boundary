import IsingBulk.HT22.Tail.NumericalEnvelopes
import IsingBulk.HT22.Algebra.BorderedMinorBound
import IsingBulk.Preferred22.NormalConvergence

/-! # Factorial normalization for odd bordered minors

An N-particle bordered determinant is (N+1)-dimensional but has the
physical normalization 1/N!. The ordinary-minor normalization cannot
simply be relabeled. This file absorbs that precise mismatch into the
fixed polynomial factor of the summable far envelope.
-/
namespace IsingBulk.HT22
noncomputable section

/-- The extra border dimension costs at most one particle factor and a
fixed exponential.  No factorial of N+1 is used in the conclusion. -/
theorem bordered_hadamard_factorial_envelope {N : ℕ} (hN : 0 < N) :
    (Real.sqrt (N+1:ℕ))^(N+1)/(N.factorial:ℝ) ≤
      (N:ℝ)*((4*Real.exp 1)/Real.sqrt N)^N := by
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have hsN : Real.sqrt (N:ℝ) ≤ N := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨hN0, ?_⟩
    nlinarith
  have hstep : Real.sqrt (N+1:ℕ) ≤ 2*Real.sqrt (N:ℝ) := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    have hsq := Real.sq_sqrt hN0
    push_cast
    nlinarith
  have htwo : (2:ℝ) ≤ 2^N := by
    simpa using (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hN)
  have hf : (0:ℝ) ≤ N.factorial := Nat.cast_nonneg _
  have hraw : (Real.sqrt (N+1:ℕ))^(N+1) ≤
      (N:ℝ)*(Real.sqrt N*4)^N := by
    calc
      _ ≤ (2*Real.sqrt (N:ℝ))^(N+1) := pow_le_pow_left₀ (Real.sqrt_nonneg _) hstep _
      _ = (2*Real.sqrt (N:ℝ))^N*(2*Real.sqrt (N:ℝ)) := pow_succ _ _
      _ ≤ (2*Real.sqrt (N:ℝ))^N*(2*(N:ℝ)) := by gcongr
      _ ≤ (2*Real.sqrt (N:ℝ))^N*(2^N*(N:ℝ)) := by gcongr
      _ = (N:ℝ)*(Real.sqrt N*4)^N := by
        rw [show (4:ℝ)=2*2 by norm_num]
        simp only [mul_pow]
        ring
  calc
    _ ≤ ((N:ℝ)*(Real.sqrt N*4)^N)/(N.factorial:ℝ) := div_le_div_of_nonneg_right hraw hf
    _ = (N:ℝ)*((Real.sqrt N*4)^N/(N.factorial:ℝ)) := by ring
    _ ≤ (N:ℝ)*((Real.exp 1*4)/Real.sqrt N)^N :=
      mul_le_mul_of_nonneg_left
        (IsingBulk.Preferred22.sqrt_factorial_envelope hN (by norm_num : (0:ℝ)≤4)) hN0
    _ = _ := by rw [mul_comm (Real.exp 1) 4]

/-- Raw bordered-minor Hadamard bounds preserve their exact remaining pair
kernel degree under the physical factorial normalization. -/
theorem bordered_minor_normalized_bound {N ell : ℕ} (hN : 0 < N)
    {a M : ℝ} (ha : 0 ≤ a)
    (hraw : M ≤ (Real.sqrt (N+1:ℕ))^(N+1)*a^(N-1-ell)) :
    M/(N.factorial:ℝ) ≤
      farOrderEnvelope (4*Real.exp 1) 1 N * a^(N-1-ell) := by
  have hf : (0:ℝ) ≤ N.factorial := Nat.cast_nonneg _
  calc
    _ ≤ ((Real.sqrt (N+1:ℕ))^(N+1)*a^(N-1-ell))/(N.factorial:ℝ) :=
      div_le_div_of_nonneg_right hraw hf
    _ = ((Real.sqrt (N+1:ℕ))^(N+1)/(N.factorial:ℝ))*a^(N-1-ell) := by ring
    _ ≤ ((N:ℝ)*((4*Real.exp 1)/Real.sqrt N)^N)*a^(N-1-ell) :=
      mul_le_mul_of_nonneg_right (bordered_hadamard_factorial_envelope hN) (pow_nonneg ha _)
    _ = _ := by simp [farOrderEnvelope, IsingBulk.Preferred22.shellOrderEnvelope]

/-- The actual ordinary-marked bordered determinant, with its sharp remaining
kernel degree and the physical N! normalization, not a renamed ordinary minor. -/
theorem borderedMarkedDeterminant_factorial_bound {N ell : ℕ} (hN : 0<N)
    (hell : ell≤N-1) (K : Matrix (Fin N) (Fin N) ℂ)
    (marks : Fin ell → Fin N × Fin N) {a : ℝ} (ha : 0<a)
    (hK : ∀ i j, ‖K i j‖≤a) :
    ‖Algebra.borderedMarkedDeterminant K marks‖/(N.factorial:ℝ) ≤
      farOrderEnvelope (4*Real.exp 1) 1 N*a^(N-1-ell) :=
  bordered_minor_normalized_bound hN ha.le
    (by simpa only [Nat.cast_add,Nat.cast_one] using
      Algebra.borderedMarkedDeterminant_hadamard hell hN K marks a ha hK)

end
end IsingBulk.HT22
