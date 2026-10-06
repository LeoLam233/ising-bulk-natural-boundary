import IsingBulk.Tail.SelectorDefinitions
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! Actual fixed-weight coordinate derivatives and named supports.
These statements do not differentiate any epsilon-dependent partition. -/
namespace IsingBulk.Tail
noncomputable section
open scoped BigOperators

 theorem angularSelector_update {N : ℕ} (f : SelectorFunctions) (θ : Fin N → ℝ)
    (q : Fin N) (u : ℝ) :
    angularSelector f (Function.update θ q u) =
      (1-f.a u)*∏ i ∈ Finset.univ.erase q, (1-f.a (θ i)) := by
  unfold angularSelector selectorWeight
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ q)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

 theorem angularSelector_coordinate_deriv {N : ℕ} (f : SelectorFunctions)
    (θ : Fin N → ℝ) (q : Fin N) (ha : DifferentiableAt ℝ f.a (θ q)) :
    deriv (fun u => angularSelector f (Function.update θ q u)) (θ q) =
      namedSelectorDerivative f q θ := by
  simp_rw [angularSelector_update]
  exact ((ha.hasDerivAt.const_sub 1).mul_const _).deriv

 theorem namedSelectorDerivative_support {N : ℕ} (f : SelectorFunctions)
    (θ : Fin N → ℝ) (q : Fin N) (h : namedSelectorDerivative f q θ ≠ 0) :
    deriv f.a (θ q) ≠ 0 ∧ ∀ i, i ≠ q → f.a (θ i) ≠ 1 := by
  have hh := mul_ne_zero_iff.mp h
  refine ⟨neg_ne_zero.mp hh.1, ?_⟩
  intro i hi he
  have hp := Finset.prod_ne_zero_iff.mp hh.2 i (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩)
  exact hp (by rw [he, sub_self])

 theorem angularSelector_support {N : ℕ} (f : SelectorFunctions)
    (θ : Fin N → ℝ) (h : angularSelector f θ ≠ 0) :
    ∀ i, f.a (θ i) ≠ 1 := by
  unfold angularSelector selectorWeight at h
  intro i he
  have hh := Finset.prod_ne_zero_iff.mp h i (Finset.mem_univ i)
  exact hh (by simp only [he, sub_self])

 theorem selected_exists_named {N : ℕ} (f : SelectorFunctions)
    (θ : Fin N → ℝ) (h : 1-angularSelector f θ ≠ 0) :
    ∃ q : Fin N, f.a (θ q) ≠ 0 := by
  by_contra hn
  push Not at hn
  apply h
  simp [angularSelector, selectorWeight, hn]

 theorem selected_occupancy_ge_one {N : ℕ} (f : SelectorFunctions)
    (θ : Fin N → ℝ) (hp : ∀ x, 0 ≤ f.p x)
    (hplateau : ∀ x, f.a x ≠ 0 → f.p x = 1)
    (h : 1-angularSelector f θ ≠ 0) :
    1 ≤ occupancy (fun i => f.p (θ i)) := by
  obtain ⟨q,hq⟩ := selected_exists_named f θ h
  exact occupancy_named (fun i => hp (θ i)) q (hplateau _ hq)

 theorem current_occupancy_ge_one {N : ℕ} (f : SelectorFunctions)
    (θ : Fin N → ℝ) (q : Fin N) (hp : ∀ x, 0 ≤ f.p x)
    (hplateau : ∀ x, deriv f.a x ≠ 0 → f.p x = 1)
    (h : namedSelectorDerivative f q θ ≠ 0) :
    1 ≤ occupancy (fun i => f.p (θ i)) := by
  exact occupancy_named (fun i => hp (θ i)) q
    (hplateau _ (namedSelectorDerivative_support f θ q h).1)

end
end IsingBulk.Tail
