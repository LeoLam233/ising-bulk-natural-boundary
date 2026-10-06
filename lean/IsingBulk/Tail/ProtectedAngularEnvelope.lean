import IsingBulk.Tail.SelectedFDiscountedWeights
import IsingBulk.Tail.OriginalDensityMajorant
import Mathlib.MeasureTheory.Integral.Pi

/-! Actual one-body envelopes separate in the angular variables. The scalar
occupancy has already been eliminated before these product integrals. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First MeasureTheory Set
open scoped BigOperators

theorem selectedOneBodyBound_eq_discount_one (b η C eps θ : ℝ) :
    selectedOneBodyBound b η C eps θ=discountedSelectedWeight b η C eps 1 θ := by
  rw [discountedSelectedWeight_eq_product]
  simp

theorem selectedOneBodyBound_integrable_integral {b η C eps : ℝ}
    (hb : 0≤b) (hbT : b≤2*Real.pi) (hC : 0≤C) (heps : 0<eps) :
    IntegrableOn (selectedOneBodyBound b η C eps) (Icc 0 (2*Real.pi)) ∧
      (∫ θ in Icc 0 (2*Real.pi), selectedOneBodyBound b η C eps θ) ≤
        4*C*Real.sqrt (2*Real.pi)+C*(2*Real.pi) := by
  have he : selectedOneBodyBound b η C eps=discountedSelectedWeight b η C eps 1 :=
    funext (selectedOneBodyBound_eq_discount_one b η C eps)
  rw [he]
  have h := discountedSelectedWeight_integrable (η := η) hb hbT hC heps le_rfl
  exact ⟨h.1,h.2.2.2⟩

theorem selectedOneBodyBound_product_integral (N : ℕ) {b η C eps : ℝ}
    (hb : 0≤b) (hbT : b≤2*Real.pi) (hC : 0≤C) (heps : 0<eps) :
    IntegrableOn (fun θ : Fin N → ℝ => ∏ i, selectedOneBodyBound b η C eps (θ i)) (angleBox N) ∧
      (∫ θ in angleBox N, ∏ i, selectedOneBodyBound b η C eps (θ i)) ≤
        (4*C*Real.sqrt (2*Real.pi)+C*(2*Real.pi))^N := by
  obtain ⟨hi,hbound⟩ := selectedOneBodyBound_integrable_integral (η := η) hb hbT hC heps
  rw [IntegrableOn,angleBox_restrict_pi]
  constructor
  · exact Integrable.fintype_prod (fun _ : Fin N => hi)
  · rw [integral_fintype_prod_eq_pow,Fintype.card_fin]
    exact pow_le_pow_left₀ (integral_nonneg (fun _ => selectedOneBodyBound_nonneg hC)) hbound N

/-- Explicit angular integration transfer; the pointwise majorant is kept as
an internal premise, never promoted to a source protected-sector theorem. -/
theorem norm_angular_integral_le_onebody_product (N : ℕ) {b η C eps A : ℝ}
    (hb : 0≤b) (hbT : b≤2*Real.pi) (hC : 0≤C) (heps : 0<eps) (hA : 0≤A)
    (F : (Fin N → ℝ) → ℂ) (hF : IntegrableOn F (angleBox N))
    (hbound : ∀ θ ∈ angleBox N, ‖F θ‖≤A*∏ i, selectedOneBodyBound b η C eps (θ i)) :
    ‖∫ θ in angleBox N, F θ‖ ≤ A*(4*C*Real.sqrt (2*Real.pi)+C*(2*Real.pi))^N := by
  obtain ⟨hi,hint⟩ := selectedOneBodyBound_product_integral N (η := η) hb hbT hC heps
  calc
    _ ≤ ∫ θ in angleBox N, ‖F θ‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ θ in angleBox N, A*∏ i, selectedOneBodyBound b η C eps (θ i) :=
      setIntegral_mono_on hF.norm (hi.const_mul A) measurableSet_Icc hbound
    _ = A*(∫ θ in angleBox N, ∏ i, selectedOneBodyBound b η C eps (θ i)) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hint hA

end
end IsingBulk.Tail
