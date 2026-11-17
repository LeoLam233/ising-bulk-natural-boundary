import IsingBulk.AnisoF002.C03.IsotropicLocalJetBounds

/-!
# Finite real-jet control under the operations in the balanced Jacobian

This quantitative calculus tracks all derivatives through a fixed order.
Finite sums contribute their actual number of summands, while products
have an explicit fixed-order binomial cost. It is used with actual smooth
periodic bump functions, not with analytic extensions of those functions.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

structure FiniteJetControl (k : ℕ) (f : E → F) (C : ℝ) : Prop where
  smooth : ContDiff ℝ k f
  bound : ∀ m : ℕ, m ≤ k → ∀ x : E, ‖iteratedFDeriv ℝ m f x‖ ≤ C

theorem FiniteJetControl.mono_bound {k : ℕ} {f : E → F} {C D : ℝ}
    (h : FiniteJetControl k f C) (hCD : C ≤ D) : FiniteJetControl k f D :=
  ⟨h.smooth, fun m hm x => (h.bound m hm x).trans hCD⟩

theorem finiteJetControl_const (k : ℕ) (c : F) (C : ℝ) (hc : ‖c‖ ≤ C) :
    FiniteJetControl k (fun _ : E => c) C := by
  refine ⟨contDiff_const, ?_⟩
  intro m _ x
  by_cases hm : m = 0
  · subst m
    simpa only [norm_iteratedFDeriv_zero] using hc
  · rw [iteratedFDeriv_const_of_ne hm]
    change ‖(0 : (E [×m]→L[ℝ] F))‖ ≤ C
    rw [norm_zero]
    exact (norm_nonneg c).trans hc

theorem FiniteJetControl.add {k : ℕ} {f g : E → F} {C D : ℝ}
    (hf : FiniteJetControl k f C) (hg : FiniteJetControl k g D) :
    FiniteJetControl k (fun x => f x + g x) (C + D) := by
  refine ⟨hf.smooth.add hg.smooth, ?_⟩
  intro m hm x
  rw [fun_iteratedFDeriv_add_apply (hf.smooth.of_le (by exact_mod_cast hm)).contDiffAt
    (hg.smooth.of_le (by exact_mod_cast hm)).contDiffAt]
  exact (norm_add_le _ _).trans (add_le_add (hf.bound m hm x) (hg.bound m hm x))

theorem FiniteJetControl.sub {k : ℕ} {f g : E → F} {C D : ℝ}
    (hf : FiniteJetControl k f C) (hg : FiniteJetControl k g D) :
    FiniteJetControl k (fun x => f x - g x) (C + D) := by
  refine ⟨hf.smooth.sub hg.smooth, ?_⟩
  intro m hm x
  rw [fun_iteratedFDeriv_sub_apply (hf.smooth.of_le (by exact_mod_cast hm)).contDiffAt
    (hg.smooth.of_le (by exact_mod_cast hm)).contDiffAt]
  exact (norm_sub_le _ _).trans (add_le_add (hf.bound m hm x) (hg.bound m hm x))

theorem FiniteJetControl.clm {k : ℕ} {f : E → F} {C : ℝ}
    (hf : FiniteJetControl k f C) (L : F →L[ℝ] G) :
    FiniteJetControl k (fun x => L (f x)) (‖L‖ * C) := by
  refine ⟨L.contDiff.comp hf.smooth, ?_⟩
  intro m hm x
  have hh := L.norm_iteratedFDeriv_comp_left (x := x) hf.smooth.contDiffAt (n := m) (by exact_mod_cast hm)
  exact hh.trans (mul_le_mul_of_nonneg_left (hf.bound m hm x) (norm_nonneg _))

theorem FiniteJetControl.comp_clm {k : ℕ} {f : F → G} {C : ℝ}
    (hf : FiniteJetControl k f C) (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1) :
    FiniteJetControl k (fun x => f (L x)) C := by
  refine ⟨hf.smooth.comp L.contDiff, ?_⟩
  intro m hm x
  change ‖iteratedFDeriv ℝ m (f ∘ L) x‖ ≤ C
  rw [L.iteratedFDeriv_comp_right hf.smooth x (by exact_mod_cast hm)]
  have hh := (iteratedFDeriv ℝ m f (L x)).norm_compContinuousLinearMap_le (fun _ : Fin m => L)
  have hp : (∏ _i : Fin m, ‖L‖) ≤ 1 := by
    exact (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun _ _ => hL)).trans_eq (by simp)
  exact hh.trans ((mul_le_of_le_one_right (norm_nonneg _) hp).trans (hf.bound m hm (L x)))

theorem FiniteJetControl.mul {k : ℕ} {f g : E → ℂ} {C D : ℝ}
    (hf : FiniteJetControl k f C) (hg : FiniteJetControl k g D)
    (hC : 0 ≤ C) (hD : 0 ≤ D) :
    FiniteJetControl k (fun x => f x * g x) (2 ^ k * C * D) := by
  refine ⟨hf.smooth.mul hg.smooth, ?_⟩
  intro m hm x
  have hh := norm_iteratedFDeriv_mul_at_le f g x m
    (hf.smooth.of_le (by exact_mod_cast hm)).contDiffAt
    (hg.smooth.of_le (by exact_mod_cast hm)).contDiffAt
  calc
    _ ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (m - i) g x‖ := hh
    _ ≤ ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * C * D := by
      apply Finset.sum_le_sum
      intro i hi
      have him : i ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hf.bound i (him.trans hm) x) (by positivity))
        (hg.bound (m - i) ((Nat.sub_le m i).trans hm) x) (norm_nonneg _) (by positivity)
    _ = (2 : ℝ) ^ m * C * D := by
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      congr 2
      exact_mod_cast Nat.sum_range_choose m
    _ ≤ 2 ^ k * C * D := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hm) hC) hD

theorem finiteJetControl_finsetSum {ι : Type*} (u : Finset ι) (k : ℕ)
    (f : ι → E → F) (C : ι → ℝ) (hf : ∀ i ∈ u, FiniteJetControl k (f i) (C i)) :
    FiniteJetControl k (fun x => ∑ i ∈ u, f i x) (∑ i ∈ u, C i) := by
  refine ⟨ContDiff.sum (fun i hi => (hf i hi).smooth), ?_⟩
  intro m hm x
  exact (norm_iteratedFDeriv_finsetSum_le u f x m (fun i hi =>
    ((hf i hi).smooth.of_le (by exact_mod_cast hm)).contDiffAt)).trans
      (Finset.sum_le_sum (fun i hi => (hf i hi).bound m hm x))

end IsingBulk.AnisoF002.Isotropic
