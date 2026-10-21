import IsingBulk.HT.Tail.SignedSectorNorms
import IsingBulk.Tail.LeftCompactSectorNorm

namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Tail Set MeasureTheory
open scoped Topology BigOperators

theorem signedOriginalLeftCompactSectorNorm_zero (ζ : ℂ) (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (k : ℕ) (s : ℂ) :
    signedOriginalLeftCompactSectorNorm ζ 0 f r τ b outer inner ho hi k s=0 := by
  simp [signedOriginalLeftCompactSectorNorm]

theorem signedIntegratedLeftCompactSectorNorm_zero (ζ : ℂ) (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (k : ℕ) (s : ℂ) (cut : ℝ) :
    signedIntegratedLeftCompactSectorNorm ζ 0 f r τ b outer inner ho hi k s cut=0 := by
  simp [signedIntegratedLeftCompactSectorNorm]

theorem signedOriginalLeftCompactSectorNorm_le (ζ : ℂ) {N : ℕ} (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (k : ℕ) (s : ℂ) {Q : ℝ} (hQ : 0≤Q)
    (hbound : ∀ (a q : Fin N) (sigma : Fin N → Fin 3),sigma a=0 → (∀ i,sigma i≠2) →
      ‖iteratedDeriv k (signedOriginalSectorIntegral ζ N f r τ b outer inner ho hi (some (q,sigma))) s‖≤Q) :
    signedOriginalLeftCompactSectorNorm ζ N f r τ b outer inner ho hi k s≤12^N*Q := by
  classical
  unfold signedOriginalLeftCompactSectorNorm
  calc
    _ ≤ ∑ _qa : Fin N × (Fin N → Fin 3),Q := by
      apply Finset.sum_le_sum
      rintro ⟨q,sigma⟩ _
      split_ifs with hσ
      · obtain ⟨hn,a,ha⟩ := hσ
        exact hbound a q sigma ha hn
      · exact hQ
    _ = (Fintype.card (Fin N × (Fin N → Fin 3)):ℝ)*Q := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (mixed_nested_label_count N) hQ

theorem signedIntegratedLeftCompactSectorNorm_le (ζ : ℂ) {N : ℕ} (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (k : ℕ) (s : ℂ) {cut Q : ℝ}
    (hcut : cut∈Icc (0:ℝ) 1) (hQ : 0≤Q)
    (hbound : ∀ (a q qA : Fin N) (sigma : Fin N → Fin 3),sigma a=0 → (∀ i,sigma i≠2) →
      ∀ lam∈Icc (0:ℝ) cut,
      ‖iteratedDeriv k (signedCurrentSectorIntegral ζ N f r τ lam q b outer inner ho hi (some (qA,sigma))) s‖≤Q) :
    signedIntegratedLeftCompactSectorNorm ζ N f r τ b outer inner ho hi k s cut≤24^N*Q := by
  classical
  have hterm (q qA : Fin N) (sigma : Fin N → Fin 3) (hσ : leftCompactAssignment sigma) :
      ‖∫ lam in 0..cut,iteratedDeriv k (signedCurrentSectorIntegral ζ N f r τ lam q b outer inner ho hi (some (qA,sigma))) s‖≤Q := by
    obtain ⟨hn,a,ha⟩ := hσ
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (C := Q) (a := (0:ℝ)) (b := cut)
      (f := fun lam => iteratedDeriv k (signedCurrentSectorIntegral ζ N f r τ lam q b outer inner ho hi (some (qA,sigma))) s) (by
        intro lam hlam
        rw [uIoc_of_le hcut.1] at hlam
        exact hbound a q qA sigma ha hn lam ⟨hlam.1.le,hlam.2⟩)
    simp only [sub_zero,abs_of_nonneg hcut.1] at hh
    exact hh.trans (mul_le_of_le_one_right hQ hcut.2)
  unfold signedIntegratedLeftCompactSectorNorm
  calc
    _ ≤ ∑ _q : Fin N,∑ _qa : Fin N × (Fin N → Fin 3),Q := by
      apply Finset.sum_le_sum
      intro q _
      apply Finset.sum_le_sum
      rintro ⟨qA,sigma⟩ _
      split_ifs with hσ
      · exact hterm q qA sigma hσ
      · exact hQ
    _ = (N:ℝ)*((Fintype.card (Fin N × (Fin N → Fin 3)):ℝ)*Q) := by simp
    _ ≤ (2:ℝ)^N*((12:ℝ)^N*Q) := by
      have hN : (N:ℝ)≤(2:ℝ)^N := by exact_mod_cast (Nat.lt_two_pow_self (n := N)).le
      exact mul_le_mul hN (mul_le_mul_of_nonneg_right (mixed_nested_label_count N) hQ)
        (by positivity) (by positivity)
    _ = _ := by rw [← mul_assoc,← mul_pow]; norm_num

end
end IsingBulk.HT.Contour
