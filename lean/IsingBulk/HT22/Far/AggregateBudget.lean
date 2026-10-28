import IsingBulk.HT22.Far.FiniteShells
import IsingBulk.HT22.Far.ConstantBudget
import IsingBulk.HT22.Geometry.SignedMean

namespace IsingBulk.HT22.Far
noncomputable section
open IsingBulk.Preferred22
open scoped BigOperators ENNReal

theorem finite_shell_label_sum_bound {N K : ℕ} (hN : 0<N)
    (f : ℕ → {l : ℤ // l∈preferredMeanIndices N} → Fin N → Fin N → ℝ≥0∞)
    (E : ℝ≥0∞) (hf : ∀ q l i k,f q l i k≤E)
    (hz : ∀ q, K≤q → ∀ l i k, f q l i k=0) :
    (∑' q, ∑ l, ∑ i, ∑ k,f q l i k) ≤ ((3*K*N^3:ℕ):ℝ≥0∞)*E := by
  have hzero : ∀ q∉Finset.range K,(∑ l,∑ i,∑ k,f q l i k)=0 := by
    intro q hq
    simp only [hz q (Nat.le_of_not_gt (by simpa using hq)),Finset.sum_const_zero]
  rw [tsum_eq_sum hzero]
  calc
    _ ≤ ∑ q∈Finset.range K,∑ _l : {l : ℤ // l∈preferredMeanIndices N},
          ∑ _i : Fin N,∑ _k : Fin N,E := by
      apply Finset.sum_le_sum
      intro q _
      apply Finset.sum_le_sum
      intro l _
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_le_sum (fun k _ => hf q l i k)
    _ = ((K*(preferredMeanIndices N).card*N*N:ℕ):ℝ≥0∞)*E := by simp [Nat.cast_mul];ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast (show K*(preferredMeanIndices N).card*N*N≤3*K*N^3 by
        have hh := Nat.mul_le_mul_left K (Geometry.signed_shell_label_count N hN)
        nlinarith)

theorem far_label_envelope_absorb {A : ℝ} (hA : 0≤A) (K L N : ℕ) (hN : 0<N) :
    (3*K*N^3:ℕ)*farOrderEnvelope A L N≤
      farOrderEnvelope ((max 1 (3*(K:ℝ)))*A) (L+3) N := by
  have he : (N:ℝ)^3*farOrderEnvelope A L N=farOrderEnvelope A (L+3) N := by
    unfold farOrderEnvelope shellOrderEnvelope
    rw [pow_add]
    ring
  calc
    _ = (3*(K:ℝ))*((N:ℝ)^3*farOrderEnvelope A L N) := by push_cast;ring
    _ = (3*(K:ℝ))*farOrderEnvelope A (L+3) N := by rw [he]
    _ ≤ max 1 (3*(K:ℝ))*farOrderEnvelope A (L+3) N :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (farOrderEnvelope_nonneg hA _ _)
    _ ≤ _ := farOrderEnvelope_absorb_factor hA (le_max_left _ _) hN _

end
end IsingBulk.HT22.Far
