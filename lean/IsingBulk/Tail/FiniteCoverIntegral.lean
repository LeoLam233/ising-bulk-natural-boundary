import IsingBulk.Tail.MixedPositiveGlobalIntegral

namespace IsingBulk.Tail
noncomputable section
open Set MeasureTheory Function
open scoped BigOperators

/-- A finite cover pays only its cardinality, even when its cells overlap.
The cover need only contain the support of the integrand inside the domain. -/
theorem finite_cover_integral_norm_le {X ι : Type*} [MeasurableSpace X]
    (μ : Measure X) (T : Finset ι) (S K : Set X) (cell : ι → Set X)
    (F : X → ℂ) (M : X → ℝ) {D Q : ℝ}
    (hS : MeasurableSet S) (hF : IntegrableOn F S μ) (hD : 0≤D)
    (hM : ∀ x,0≤M x) (hc : ∀ i∈T,MeasurableSet (cell i))
    (hi : ∀ i∈T,IntegrableOn M (cell i) μ)
    (hQ : ∀ i∈T,(∫ x in cell i,M x ∂μ)≤Q)
    (hsupp : support F⊆K)
    (hcover : ∀ x∈S, x∈K → ∃ i∈T,x∈cell i)
    (hpoint : ∀ x∈S,x∈K → ‖F x‖≤D*M x) :
    (∫ x in S,‖F x‖ ∂μ)≤D*((T.card:ℝ)*Q) := by
  classical
  let G := fun x => ∑ i∈T,(cell i).indicator (fun y => D*M y) x
  have hgi (i : ι) (hiT : i∈T) : Integrable ((cell i).indicator (fun x => D*M x)) μ :=
    (integrable_indicator_iff (hc i hiT)).mpr ((hi i hiT).const_mul D)
  have hG : Integrable G μ := integrable_finsetSum T (fun i hiT => hgi i hiT)
  have hG0 (x : X) : 0≤G x := by
    apply Finset.sum_nonneg
    intro i _
    exact indicator_nonneg (fun y _ => mul_nonneg hD (hM y)) x
  have hFG (x : X) (hx : x∈S) : ‖F x‖≤G x := by
    by_cases hFx : F x=0
    · simpa only [hFx,norm_zero] using hG0 x
    · have hxK := hsupp hFx
      obtain ⟨i,hiT,hxi⟩ := hcover x hx hxK
      apply (hpoint x hx hxK).trans
      have hh := Finset.single_le_sum (fun i (_ : i∈T) =>
        indicator_nonneg (s := cell i) (fun y _ => mul_nonneg hD (hM y)) x) hiT
      simpa only [indicator_of_mem hxi] using hh
  calc
    _ ≤ ∫ x in S,G x ∂μ := setIntegral_mono_on hF.norm hG.integrableOn hS hFG
    _ ≤ ∫ x,G x ∂μ := setIntegral_le_integral hG (Filter.Eventually.of_forall hG0)
    _ = ∑ i∈T,D*(∫ x in cell i,M x ∂μ) := by
      rw [show G=(fun x => ∑ i∈T,(cell i).indicator (fun y => D*M y) x) from rfl,
        integral_finsetSum T (fun i hiT => hgi i hiT)]
      apply Finset.sum_congr rfl
      intro i hiT
      rw [integral_indicator (hc i hiT),integral_const_mul]
    _ ≤ ∑ _i∈T,D*Q := Finset.sum_le_sum (fun i hiT => mul_le_mul_of_nonneg_left (hQ i hiT) hD)
    _ = _ := by simp [Finset.sum_const,nsmul_eq_mul]; ring

end
end IsingBulk.Tail
