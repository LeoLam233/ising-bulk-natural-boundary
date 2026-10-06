import IsingBulk.Tail.MixedSectorNorm

namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First Set MeasureTheory
open scoped Topology BigOperators

def leftCompactAssignment {N : ℕ} (sigma : Fin N → Fin 3) : Prop :=
  (∀ i,sigma i≠2) ∧ ∃ a,sigma a=0

def originalLeftCompactSectorNorm (N : ℕ) (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (k : ℕ) (s : ℂ) : ℝ := by
  classical
  exact ∑ qa : Fin N × (Fin N → Fin 3), if leftCompactAssignment qa.2 then
    ‖iteratedDeriv k (originalSectorIntegral N f r τ b outer inner ho hi (some qa)) s‖ else 0

def integratedLeftCompactSectorNorm (N : ℕ) (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (k : ℕ) (s : ℂ) (cut : ℝ) : ℝ := by
  classical
  exact ∑ q : Fin N,∑ qa : Fin N × (Fin N → Fin 3), if leftCompactAssignment qa.2 then
    ‖∫ lam in 0..cut,iteratedDeriv k (currentSectorIntegral N f r τ lam q b outer inner ho hi (some qa)) s‖ else 0

theorem originalLeftCompactSectorNorm_nonneg (N : ℕ) (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (k : ℕ) (s : ℂ) :
    0≤originalLeftCompactSectorNorm N f r τ b outer inner ho hi k s := by
  classical
  unfold originalLeftCompactSectorNorm
  exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)

theorem integratedLeftCompactSectorNorm_nonneg (N : ℕ) (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (k : ℕ) (s : ℂ) (cut : ℝ) :
    0 ≤ integratedLeftCompactSectorNorm N f r τ b outer inner ho hi k s cut := by
  classical
  unfold integratedLeftCompactSectorNorm
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity))

theorem originalLeftCompactSectorNorm_zero (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (k : ℕ) (s : ℂ) :
    originalLeftCompactSectorNorm 0 f r τ b outer inner ho hi k s=0 := by
  simp [originalLeftCompactSectorNorm]

theorem integratedLeftCompactSectorNorm_zero (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (k : ℕ) (s : ℂ) (cut : ℝ) :
    integratedLeftCompactSectorNorm 0 f r τ b outer inner ho hi k s cut=0 := by
  simp [integratedLeftCompactSectorNorm]

theorem originalLeftCompactSectorNorm_le {N : ℕ} (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (k : ℕ) (s : ℂ) {Q : ℝ} (hQ : 0≤Q)
    (hbound : ∀ (a q : Fin N) (sigma : Fin N → Fin 3),sigma a=0 → (∀ i,sigma i≠2) →
      ‖iteratedDeriv k (originalSectorIntegral N f r τ b outer inner ho hi (some (q,sigma))) s‖≤Q) :
    originalLeftCompactSectorNorm N f r τ b outer inner ho hi k s≤12^N*Q := by
  classical
  unfold originalLeftCompactSectorNorm
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

theorem integratedLeftCompactSectorNorm_le {N : ℕ} (f : SelectorFunctions) (r τ b outer inner : ℝ)
    (ho : 0<outer) (hi : 0< inner) (k : ℕ) (s : ℂ) {cut Q : ℝ}
    (hcut : cut∈Icc (0:ℝ) 1) (hQ : 0≤Q)
    (hbound : ∀ (a q qA : Fin N) (sigma : Fin N → Fin 3),sigma a=0 → (∀ i,sigma i≠2) →
      ∀ lam∈Icc (0:ℝ) cut,
      ‖iteratedDeriv k (currentSectorIntegral N f r τ lam q b outer inner ho hi (some (qA,sigma))) s‖≤Q) :
    integratedLeftCompactSectorNorm N f r τ b outer inner ho hi k s cut≤24^N*Q := by
  classical
  have hterm (q qA : Fin N) (sigma : Fin N → Fin 3) (hσ : leftCompactAssignment sigma) :
      ‖∫ lam in 0..cut,iteratedDeriv k (currentSectorIntegral N f r τ lam q b outer inner ho hi (some (qA,sigma))) s‖≤Q := by
    obtain ⟨hn,a,ha⟩ := hσ
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (C := Q) (a := (0:ℝ)) (b := cut)
      (f := fun lam => iteratedDeriv k (currentSectorIntegral N f r τ lam q b outer inner ho hi (some (qA,sigma))) s) (by
        intro lam hlam
        rw [uIoc_of_le hcut.1] at hlam
        exact hbound a q qA sigma ha hn lam ⟨hlam.1.le,hlam.2⟩)
    simp only [sub_zero,abs_of_nonneg hcut.1] at hh
    exact hh.trans (mul_le_of_le_one_right hQ hcut.2)
  unfold integratedLeftCompactSectorNorm
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
end IsingBulk.Tail
