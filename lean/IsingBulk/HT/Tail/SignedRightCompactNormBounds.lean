import IsingBulk.Tail.RightCompactSectorNorm
import IsingBulk.HT.Tail.SignedSectorNorms

namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Tail Set MeasureTheory
open scoped Topology BigOperators

theorem signedOriginalRightCompactSectorNorm_le (σ : ℂ) {N : ℕ} (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0 < outer) (hi : 0 < inner) (k : ℕ) (s : ℂ) {Q : ℝ} (hQ : 0 ≤ Q)
    (hbound : ∀ (q : Fin N) (sigma : Fin N → Fin 3), (∀ i, sigma i=1) →
      ‖iteratedDeriv k (signedOriginalSectorIntegral σ N f r τ b outer inner ho hi (some (q,sigma))) s‖ ≤ Q) :
    signedOriginalRightCompactSectorNorm σ N f r τ b outer inner ho hi k s ≤ compactSectorMultiplicity N*Q := by
  classical
  unfold signedOriginalRightCompactSectorNorm
  calc
    _ ≤ ∑ _qa : Fin N × (Fin N → Fin 3), Q := by
      apply Finset.sum_le_sum
      rintro ⟨q,sigma⟩ _
      split_ifs with hσ
      · exact hbound q sigma hσ
      · exact hQ
    _ = (Fintype.card (Fin N × (Fin N → Fin 3)):ℝ)*Q := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right ((mixed_nested_label_count N).trans (compactSectorMultiplicity_original N)) hQ

theorem signedIntegratedRightCompactSectorNorm_le (σ : ℂ) {N : ℕ} (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0 < outer) (hi : 0 < inner) (k : ℕ) (s : ℂ) {cut Q : ℝ}
    (hcut : cut ∈ Icc (0:ℝ) 1) (hQ : 0 ≤ Q)
    (hbound : ∀ (q qA : Fin N) (sigma : Fin N → Fin 3), (∀ i, sigma i=1) →
      ∀ lam ∈ Icc (0:ℝ) cut,
      ‖iteratedDeriv k (signedCurrentSectorIntegral σ N f r τ lam q b outer inner ho hi (some (qA,sigma))) s‖ ≤ Q) :
    signedIntegratedRightCompactSectorNorm σ N f r τ b outer inner ho hi k s cut ≤ compactSectorMultiplicity N*Q := by
  classical
  have hterm (q qA : Fin N) (sigma : Fin N → Fin 3) (hσ : ∀ i, sigma i=1) :
      ‖∫ lam in 0..cut, iteratedDeriv k (signedCurrentSectorIntegral σ N f r τ lam q b outer inner ho hi (some (qA,sigma))) s‖ ≤ Q := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (C := Q) (a := (0:ℝ)) (b := cut)
      (f := fun lam => iteratedDeriv k (signedCurrentSectorIntegral σ N f r τ lam q b outer inner ho hi (some (qA,sigma))) s) (by
        intro lam hlam
        rw [uIoc_of_le hcut.1] at hlam
        exact hbound q qA sigma hσ lam ⟨hlam.1.le,hlam.2⟩)
    simp only [sub_zero,abs_of_nonneg hcut.1] at hh
    exact hh.trans (mul_le_of_le_one_right hQ hcut.2)
  unfold signedIntegratedRightCompactSectorNorm
  calc
    _ ≤ ∑ _q : Fin N, ∑ _qa : Fin N × (Fin N → Fin 3), Q := by
      apply Finset.sum_le_sum
      intro q _
      apply Finset.sum_le_sum
      rintro ⟨qA,sigma⟩ _
      split_ifs with hσ
      · exact hterm q qA sigma hσ
      · exact hQ
    _ = ((N:ℝ)*(Fintype.card (Fin N × (Fin N → Fin 3)):ℝ))*Q := by simp [mul_assoc]
    _ ≤ ((N:ℝ)*12^N)*Q := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (mixed_nested_label_count N) (Nat.cast_nonneg N)) hQ
    _ ≤ _ := mul_le_mul_of_nonneg_right (compactSectorMultiplicity_current N) hQ

end
end IsingBulk.HT.Tail
