import IsingBulk.Tail.MixedSectorNorm
import IsingBulk.Tail.WeightedCompactSourceMajorant

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First Set MeasureTheory
open scoped Topology BigOperators

def originalRightCompactSectorNorm (N : ℕ) (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0 < outer) (hi : 0 < inner) (k : ℕ) (s : ℂ) : ℝ := by
  classical
  exact ∑ qa : Fin N × (Fin N → Fin 3), if ∀ i, qa.2 i=1 then
    ‖iteratedDeriv k (originalSectorIntegral N f r τ b outer inner ho hi (some qa)) s‖ else 0

def integratedRightCompactSectorNorm (N : ℕ) (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0 < outer) (hi : 0 < inner) (k : ℕ) (s : ℂ) (cut : ℝ) : ℝ := by
  classical
  exact ∑ q : Fin N, ∑ qa : Fin N × (Fin N → Fin 3), if ∀ i, qa.2 i=1 then
    ‖∫ lam in 0..cut, iteratedDeriv k (currentSectorIntegral N f r τ lam q b outer inner ho hi (some qa)) s‖ else 0

theorem originalRightCompactSectorNorm_nonneg (N : ℕ) (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0 < outer) (hi : 0 < inner) (k : ℕ) (s : ℂ) :
    0 ≤ originalRightCompactSectorNorm N f r τ b outer inner ho hi k s := by
  classical
  unfold originalRightCompactSectorNorm
  exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)

theorem integratedRightCompactSectorNorm_nonneg (N : ℕ) (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0 < outer) (hi : 0 < inner) (k : ℕ) (s : ℂ) (cut : ℝ) :
    0 ≤ integratedRightCompactSectorNorm N f r τ b outer inner ho hi k s cut := by
  classical
  unfold integratedRightCompactSectorNorm
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity))

theorem originalRightCompactSectorNorm_zero (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0 < outer) (hi : 0 < inner) (k : ℕ) (s : ℂ) :
    originalRightCompactSectorNorm 0 f r τ b outer inner ho hi k s=0 := by simp [originalRightCompactSectorNorm]

theorem integratedRightCompactSectorNorm_zero (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0 < outer) (hi : 0 < inner) (k : ℕ) (s : ℂ) (cut : ℝ) :
    integratedRightCompactSectorNorm 0 f r τ b outer inner ho hi k s cut=0 := by simp [integratedRightCompactSectorNorm]

theorem compactSectorMultiplicity_original (N : ℕ) : (12:ℝ)^N ≤ compactSectorMultiplicity N := by
  cases N with
  | zero => norm_num [compactSectorMultiplicity]
  | succ n =>
    have hn : (1:ℝ) ≤ (n+1:ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hh := mul_le_mul_of_nonneg_left (one_le_pow₀ hn (n := 2)) (by positivity : 0 ≤ (12:ℝ)^(n+1))
    unfold compactSectorMultiplicity
    nlinarith

theorem compactSectorMultiplicity_current (N : ℕ) : (N:ℝ)*(12:ℝ)^N ≤ compactSectorMultiplicity N := by
  cases N with
  | zero => norm_num [compactSectorMultiplicity]
  | succ n =>
    have hn : (1:ℝ) ≤ (n+1:ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hh := mul_le_mul_of_nonneg_left (show (n+1:ℕ) ≤ ((n+1:ℕ):ℝ)^2 by nlinarith)
      (by positivity : 0 ≤ (12:ℝ)^(n+1))
    unfold compactSectorMultiplicity
    nlinarith

theorem originalRightCompactSectorNorm_le {N : ℕ} (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0 < outer) (hi : 0 < inner) (k : ℕ) (s : ℂ) {Q : ℝ} (hQ : 0 ≤ Q)
    (hbound : ∀ (q : Fin N) (sigma : Fin N → Fin 3), (∀ i, sigma i=1) →
      ‖iteratedDeriv k (originalSectorIntegral N f r τ b outer inner ho hi (some (q,sigma))) s‖ ≤ Q) :
    originalRightCompactSectorNorm N f r τ b outer inner ho hi k s ≤ compactSectorMultiplicity N*Q := by
  classical
  unfold originalRightCompactSectorNorm
  calc
    _ ≤ ∑ _qa : Fin N × (Fin N → Fin 3), Q := by
      apply Finset.sum_le_sum
      rintro ⟨q,sigma⟩ _
      split_ifs with hσ
      · exact hbound q sigma hσ
      · exact hQ
    _ = (Fintype.card (Fin N × (Fin N → Fin 3)):ℝ)*Q := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right ((mixed_nested_label_count N).trans (compactSectorMultiplicity_original N)) hQ

theorem integratedRightCompactSectorNorm_le {N : ℕ} (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0 < outer) (hi : 0 < inner) (k : ℕ) (s : ℂ) {cut Q : ℝ}
    (hcut : cut ∈ Icc (0:ℝ) 1) (hQ : 0 ≤ Q)
    (hbound : ∀ (q qA : Fin N) (sigma : Fin N → Fin 3), (∀ i, sigma i=1) →
      ∀ lam ∈ Icc (0:ℝ) cut,
      ‖iteratedDeriv k (currentSectorIntegral N f r τ lam q b outer inner ho hi (some (qA,sigma))) s‖ ≤ Q) :
    integratedRightCompactSectorNorm N f r τ b outer inner ho hi k s cut ≤ compactSectorMultiplicity N*Q := by
  classical
  have hterm (q qA : Fin N) (sigma : Fin N → Fin 3) (hσ : ∀ i, sigma i=1) :
      ‖∫ lam in 0..cut, iteratedDeriv k (currentSectorIntegral N f r τ lam q b outer inner ho hi (some (qA,sigma))) s‖ ≤ Q := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (C := Q) (a := (0:ℝ)) (b := cut)
      (f := fun lam => iteratedDeriv k (currentSectorIntegral N f r τ lam q b outer inner ho hi (some (qA,sigma))) s) (by
        intro lam hlam
        rw [uIoc_of_le hcut.1] at hlam
        exact hbound q qA sigma hσ lam ⟨hlam.1.le,hlam.2⟩)
    simp only [sub_zero,abs_of_nonneg hcut.1] at hh
    exact hh.trans (mul_le_of_le_one_right hQ hcut.2)
  unfold integratedRightCompactSectorNorm
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
end IsingBulk.Tail
