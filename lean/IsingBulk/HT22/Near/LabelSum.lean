import IsingBulk.HT22.Geometry.SignedMean
import IsingBulk.HT22.Near.QuadraticAbsorption

namespace IsingBulk.HT22.Near
noncomputable section
open IsingBulk.Preferred22
open scoped BigOperators ENNReal

theorem infinite_shell_label_sum_bound {N : ℕ} (hN : 0<N)
    (f : ℕ → {l : ℤ // l∈preferredMeanIndices N} → Fin N → Fin N → ℝ≥0∞)
    (E : ℝ≥0∞) (hf : ∀ l i k,(∑' q,f q l i k)≤E) :
    (∑' q,∑ l,∑ i,∑ k,f q l i k)≤((3*N^3:ℕ):ℝ≥0∞)*E := by
  have hswap : (∑' q,∑ l,∑ i,∑ k,f q l i k)=(∑ l,∑ i,∑ k,∑' q,f q l i k) := by
    simp_rw [←tsum_fintype (L := .unconditional _)]
    rw [ENNReal.tsum_comm]
    apply tsum_congr
    intro l
    rw [ENNReal.tsum_comm]
    apply tsum_congr
    intro i
    rw [ENNReal.tsum_comm]
  rw [hswap]
  calc
    _ ≤ ∑ _l : {l : ℤ // l∈preferredMeanIndices N},∑ _i : Fin N,∑ _k : Fin N,E := by
      apply Finset.sum_le_sum
      intro l _
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_le_sum (fun k _ => hf l i k)
    _ = (((preferredMeanIndices N).card*N*N:ℕ):ℝ≥0∞)*E := by simp [Nat.cast_mul];ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast Geometry.signed_shell_label_count N hN) (by positivity)

theorem near_label_quadratic_absorb {E : ℝ} (hE : 1≤E) :
    ∃ F : ℝ,1≤F ∧ ∀ N : ℕ,0<N → (3*(N:ℝ)^3)*E^(N^2)≤F^(N^2) := by
  obtain ⟨F,hF,hb⟩ := quadratic_prefactor_absorption
    (by norm_num : (0:ℝ)≤3) (by norm_num : (0:ℝ)≤1)
    (le_trans (by norm_num) hE) (by norm_num : (0:ℝ)≤1) 3
  refine ⟨F,hF,?_⟩
  intro N hN
  simpa only [one_pow,mul_one,one_mul,mul_comm,mul_left_comm,mul_assoc] using hb N hN

end
end IsingBulk.HT22.Near
