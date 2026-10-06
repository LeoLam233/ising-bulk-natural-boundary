import IsingBulk.Tail.MixedSectorExclusion
import IsingBulk.Tail.MixedGaussianIntegralBudget

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First MeasureTheory Set
open scoped BigOperators Topology

/-- Absolute finite sum of the original nested sectors containing a branch. -/
def originalMixedSectorNorm (N : ℕ) (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (k : ℕ) (s : ℂ) : ℝ := by
  classical
  exact ∑ qa : Fin N × (Fin N → Fin 3), if ∃ j,qa.2 j=2 then
    ‖iteratedDeriv k (originalSectorIntegral N f r τ b outer inner ho hi (some qa)) s‖ else 0

/-- The corresponding finite current sum, with the homotopy integral
applied after the literal parameter derivative in each sector. -/
def integratedMixedSectorNorm (N : ℕ) (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (k : ℕ) (s : ℂ) (cut : ℝ) : ℝ := by
  classical
  exact ∑ q : Fin N,∑ qa : Fin N × (Fin N → Fin 3), if ∃ j,qa.2 j=2 then
    ‖∫ lam in 0..cut,iteratedDeriv k (currentSectorIntegral N f r τ lam q b outer inner ho hi (some qa)) s‖ else 0

theorem originalMixedSectorNorm_nonneg (N : ℕ) (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (k : ℕ) (s : ℂ) :
    0≤originalMixedSectorNorm N f r τ b outer inner ho hi k s := by
  classical
  unfold originalMixedSectorNorm
  exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)

theorem integratedMixedSectorNorm_nonneg (N : ℕ) (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (k : ℕ) (s : ℂ) (cut : ℝ) :
    0 ≤ integratedMixedSectorNorm N f r τ b outer inner ho hi k s cut := by
  classical
  unfold integratedMixedSectorNorm
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity))

theorem mixed_nested_label_count (N : ℕ) :
    (Fintype.card (Fin N × (Fin N → Fin 3)):ℝ)≤(12:ℝ)^N := by
  have h := nested_sector_label_count N
  simp only [Fintype.card_option] at h
  exact_mod_cast (show Fintype.card (Fin N × (Fin N → Fin 3))≤12^N by omega)

theorem originalMixedSectorNorm_le {N : ℕ} (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (hio : inner≤outer/4) (k : ℕ) (s : ℂ) {Q : ℝ} (hQ : 0≤Q)
    (hbound : ∀ (j q : Fin N) (sigma : Fin N → Fin 3),sigma j=2 → sigma q≠2 →
      ‖iteratedDeriv k (originalSectorIntegral N f r τ b outer inner ho hi (some (q,sigma))) s‖≤Q) :
    originalMixedSectorNorm N f r τ b outer inner ho hi k s≤12^N*Q := by
  classical
  unfold originalMixedSectorNorm
  calc
    _ ≤ ∑ _qa : Fin N × (Fin N → Fin 3),Q := by
      apply Finset.sum_le_sum
      rintro ⟨q,sigma⟩ _
      split_ifs with hj
      · obtain ⟨j,hj⟩ := hj
        by_cases hq : sigma q=2
        · rw [originalSectorIntegral_eq_zero_of_anchor_branch f r τ b outer inner ho hi hio q sigma hq]
          simpa using hQ
        · exact hbound j q sigma hj hq
      · exact hQ
    _ = (Fintype.card (Fin N × (Fin N → Fin 3)):ℝ)*Q := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (mixed_nested_label_count N) hQ

theorem integratedMixedSectorNorm_le {N : ℕ} (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (k : ℕ) (s : ℂ) {cut Q : ℝ}
    (hcut : cut∈Icc (0:ℝ) 1) (hQ : 0≤Q)
    (hzero : ∀ (q qA : Fin N) (sigma : Fin N → Fin 3),sigma q=2 →
      ∀ lam∈Icc (0:ℝ) cut,currentSectorIntegral N f r τ lam q b outer inner ho hi (some (qA,sigma))=0)
    (hbound : ∀ (j q qA : Fin N) (sigma : Fin N → Fin 3),sigma j=2 → sigma q≠2 →
      ∀ lam∈Icc (0:ℝ) cut,
      ‖iteratedDeriv k (currentSectorIntegral N f r τ lam q b outer inner ho hi (some (qA,sigma))) s‖≤Q) :
    integratedMixedSectorNorm N f r τ b outer inner ho hi k s cut≤24^N*Q := by
  classical
  have hterm (q qA : Fin N) (sigma : Fin N → Fin 3) (hj : ∃ j,sigma j=2) :
      ‖∫ lam in 0..cut,iteratedDeriv k (currentSectorIntegral N f r τ lam q b outer inner ho hi (some (qA,sigma))) s‖≤Q := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (C := Q) (a := (0:ℝ)) (b := cut)
      (f := fun lam => iteratedDeriv k (currentSectorIntegral N f r τ lam q b outer inner ho hi (some (qA,sigma))) s) (by
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
  unfold integratedMixedSectorNorm
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

end
end IsingBulk.Tail
