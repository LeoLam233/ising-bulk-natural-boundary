import IsingBulk.First.ComplementFiniteAuxiliary

/-! The small auxiliary cube and integration-by-parts tail share one genuinely
integrable full-space majorant. -/
namespace IsingBulk.First
noncomputable section
open MeasureTheory Set
open scoped BigOperators

theorem auxiliary_small_large_majorant {ι : Type*} [Fintype ι]
    (F : (ι → ℝ) → ℂ) (C₀ C₁ : ℝ) (hC₀ : 0 ≤ C₀) (_hC₁ : 0 ≤ C₁)
    (hsmall : ∀ ξ ∈ Icc (0 : ι → ℝ) 1, ‖F ξ‖ ≤ C₀)
    (hlarge : ∀ ξ ∈ finiteAuxiliaryTail ι,
      ‖F ξ‖ ≤ (finiteAuxiliaryRadius ξ)⁻¹^(Fintype.card ι+1)*C₁)
    (ξ : ι → ℝ) (hξ : ∀ i, 0 ≤ ξ i) :
    ‖F ξ‖ ≤ ((2 : ℝ)^(Fintype.card ι+1)*max C₀ C₁) *
      (1+‖ξ‖)^(-((Fintype.card ι : ℝ)+1)) := by
  rw [← finite_auxiliary_majorant_power_eq]
  by_cases hR : 1 ≤ finiteAuxiliaryRadius ξ
  · calc
      _ ≤ (finiteAuxiliaryRadius ξ)⁻¹^(Fintype.card ι+1)*C₁ := hlarge ξ ⟨hξ,hR⟩
      _ ≤ ((2 : ℝ)^(Fintype.card ι+1)*(1+‖ξ‖)⁻¹^(Fintype.card ι+1))*C₁ :=
        mul_le_mul_of_nonneg_right (finite_auxiliary_tail_power_bound ⟨hξ,hR⟩) _hC₁
      _ ≤ ((2 : ℝ)^(Fintype.card ι+1)*(1+‖ξ‖)⁻¹^(Fintype.card ι+1))*max C₀ C₁ :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
      _ = _ := by ring
  · have hRle : finiteAuxiliaryRadius ξ ≤ 1 := le_of_not_ge hR
    have hc : ξ ∈ Icc (0 : ι → ℝ) 1 := ⟨hξ,fun i =>
      (Finset.single_le_sum (fun k _ => hξ k) (Finset.mem_univ i)).trans hRle⟩
    have hn : ‖ξ‖ ≤ 1 := (norm_le_finiteAuxiliaryRadius hξ).trans hRle
    have hb : 1 ≤ 2*(1+‖ξ‖)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : 0 < 1+‖ξ‖)]
      linarith
    have hp : 1 ≤ (2 : ℝ)^(Fintype.card ι+1)*(1+‖ξ‖)⁻¹^(Fintype.card ι+1) := by
      simpa only [mul_pow] using (one_le_pow₀ hb (n := Fintype.card ι+1))
    calc
      _ ≤ C₀ := hsmall ξ hc
      _ ≤ ((2 : ℝ)^(Fintype.card ι+1)*(1+‖ξ‖)⁻¹^(Fintype.card ι+1))*C₀ := by nlinarith
      _ ≤ ((2 : ℝ)^(Fintype.card ι+1)*(1+‖ξ‖)⁻¹^(Fintype.card ι+1))*max C₀ C₁ :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
      _ = _ := by ring

theorem auxiliary_small_large_majorant_integrable (ι : Type*) [Fintype ι] (C₀ C₁ : ℝ) :
    Integrable (fun ξ : ι → ℝ => ((2 : ℝ)^(Fintype.card ι+1)*max C₀ C₁) *
      (1+‖ξ‖)^(-((Fintype.card ι : ℝ)+1))) :=
  (finite_auxiliary_decay_integrable ι).const_mul _

end
end IsingBulk.First
