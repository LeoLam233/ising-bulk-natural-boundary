import IsingBulk.HT.Tail.SignedMixedSectorExclusion
import IsingBulk.HT.Tail.SignedSectorNorms

namespace IsingBulk.HT.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail IsingBulk.HT.Contour Set MeasureTheory Filter Asymptotics
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false

theorem signedOriginalMixedSectorNorm_le (ζ : ℂ) {N : ℕ} (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (hio : inner≤outer/4) (k : ℕ) (s : ℂ) {Q : ℝ} (hQ : 0≤Q)
    (hbound : ∀ (j q : Fin N) (sigma : Fin N → Fin 3),sigma j=2 → sigma q≠2 →
      ‖iteratedDeriv k (signedOriginalSectorIntegral ζ N f r τ b outer inner ho hi (some (q,sigma))) s‖≤Q) :
    signedOriginalMixedSectorNorm ζ N f r τ b outer inner ho hi k s≤12^N*Q := by
  classical
  unfold signedOriginalMixedSectorNorm
  calc
    _ ≤ ∑ _qa : Fin N × (Fin N → Fin 3),Q := by
      apply Finset.sum_le_sum
      rintro ⟨q,sigma⟩ _
      split_ifs with hj
      · obtain ⟨j,hj⟩ := hj
        by_cases hq : sigma q=2
        · rw [signed_originalSectorIntegral_eq_zero_of_anchor_branch ζ f r τ b outer inner ho hi hio q sigma hq]
          simpa using hQ
        · exact hbound j q sigma hj hq
      · exact hQ
    _ = (Fintype.card (Fin N × (Fin N → Fin 3)):ℝ)*Q := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (mixed_nested_label_count N) hQ

theorem signedIntegratedMixedSectorNorm_le (ζ : ℂ) {N : ℕ} (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (k : ℕ) (s : ℂ) {cut Q : ℝ}
    (hcut : cut∈Icc (0:ℝ) 1) (hQ : 0≤Q)
    (hzero : ∀ (q qA : Fin N) (sigma : Fin N → Fin 3),sigma q=2 →
      ∀ lam∈Icc (0:ℝ) cut,signedCurrentSectorIntegral ζ N f r τ lam q b outer inner ho hi (some (qA,sigma))=0)
    (hbound : ∀ (j q qA : Fin N) (sigma : Fin N → Fin 3),sigma j=2 → sigma q≠2 →
      ∀ lam∈Icc (0:ℝ) cut,
      ‖iteratedDeriv k (signedCurrentSectorIntegral ζ N f r τ lam q b outer inner ho hi (some (qA,sigma))) s‖≤Q) :
    signedIntegratedMixedSectorNorm ζ N f r τ b outer inner ho hi k s cut≤24^N*Q := by
  classical
  have hterm (q qA : Fin N) (sigma : Fin N → Fin 3) (hj : ∃ j,sigma j=2) :
      ‖∫ lam in 0..cut,iteratedDeriv k (signedCurrentSectorIntegral ζ N f r τ lam q b outer inner ho hi (some (qA,sigma))) s‖≤Q := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (C := Q) (a := (0:ℝ)) (b := cut)
      (f := fun lam => iteratedDeriv k (signedCurrentSectorIntegral ζ N f r τ lam q b outer inner ho hi (some (qA,sigma))) s) (by
        intro lam hlam
        have hl : lam∈Icc (0:ℝ) cut := by
          rw [uIoc_of_le hcut.1] at hlam
          exact ⟨hlam.1.le,hlam.2⟩
        by_cases hq : sigma q=2
        · rw [hzero q qA sigma hq lam hl]
          simpa using hQ
        · obtain ⟨j,hj⟩ := hj
          exact hbound j q qA sigma hj hq lam hl)
    simp only [sub_zero,abs_of_nonneg hcut.1] at hh
    exact hh.trans (mul_le_of_le_one_right hQ hcut.2)
  unfold signedIntegratedMixedSectorNorm
  calc
    _ ≤ ∑ _q : Fin N,∑ _qa : Fin N × (Fin N → Fin 3),Q := by
      apply Finset.sum_le_sum
      intro q _
      apply Finset.sum_le_sum
      rintro ⟨qA,sigma⟩ _
      split_ifs with hj
      · exact hterm q qA sigma hj
      · exact hQ
    _ = (N:ℝ)*((Fintype.card (Fin N × (Fin N → Fin 3)):ℝ)*Q) := by simp
    _ ≤ (2:ℝ)^N*((12:ℝ)^N*Q) := by
      have hN : (N:ℝ)≤(2:ℝ)^N := by exact_mod_cast (Nat.lt_two_pow_self (n := N)).le
      exact mul_le_mul hN (mul_le_mul_of_nonneg_right (mixed_nested_label_count N) hQ)
        (by positivity) (by positivity)
    _ = _ := by rw [← mul_assoc,← mul_pow]; norm_num

theorem signedOriginalMixedSectorNorm_zero (ζ : ℂ) (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (k : ℕ) (s : ℂ) :
    signedOriginalMixedSectorNorm ζ 0 f r τ b outer inner ho hi k s = 0 := by
  simp [signedOriginalMixedSectorNorm]

theorem signedIntegratedMixedSectorNorm_zero (ζ : ℂ) (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (k : ℕ) (s : ℂ) (cut : ℝ) :
    signedIntegratedMixedSectorNorm ζ 0 f r τ b outer inner ho hi k s cut = 0 := by
  simp [signedIntegratedMixedSectorNorm]

end
end IsingBulk.HT.Tail
