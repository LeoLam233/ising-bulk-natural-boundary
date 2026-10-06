import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace IsingBulk.Tail
noncomputable section
open Set MeasureTheory
open scoped BigOperators

theorem setIntegral_le_finite_cover {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    {μ : Measure X} {f : X → ℝ} {S : Set X} (hS : MeasurableSet S)
    (hf : IntegrableOn f S μ) (hf0 : ∀ x, 0 ≤ f x) (cell : ι → Set X)
    (hcell : ∀ i, MeasurableSet (cell i)) (hi : ∀ i, IntegrableOn f (cell i) μ)
    (hcover : ∀ x ∈ S, ∃ i, x ∈ cell i) :
    (∫ x in S, f x ∂μ) ≤ ∑ i, ∫ x in cell i, f x ∂μ := by
  classical
  let g := fun i => (cell i).indicator f
  have hgi (i : ι) : Integrable (g i) μ := (integrable_indicator_iff (hcell i)).mpr (hi i)
  have hsum : Integrable (fun x => ∑ i, g i x) μ := integrable_finsetSum _ (fun i _ => hgi i)
  have hg0 (i : ι) (x : X) : 0 ≤ g i x := indicator_nonneg (fun y _ => hf0 y) x
  have hp (x : X) : S.indicator f x ≤ ∑ i, g i x := by
    by_cases hx : x ∈ S
    · obtain ⟨i,hi⟩ := hcover x hx
      have hh := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => hg0 j x) (Finset.mem_univ i)
      rwa [indicator_of_mem hx,show g i x=f x from indicator_of_mem hi f] at *
    · rw [indicator_of_notMem hx]
      exact Finset.sum_nonneg (fun i _ => hg0 i x)
  rw [← integral_indicator hS]
  apply (integral_mono ((integrable_indicator_iff hS).mpr hf) hsum hp).trans_eq
  rw [integral_finsetSum _ (fun i _ => hgi i)]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_indicator (hcell i)

end
end IsingBulk.Tail
