import IsingBulk.HT.Contour.SignedContinuation
import IsingBulk.Tail.ProtectedCurrentIntegrability

/-! Actual signed named-current angular integrability and one-body
integration on the closed support of the fixed real multiplier. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Tail Set MeasureTheory
open scoped ContDiff BigOperators
set_option maxHeartbeats 1000000

theorem signed_continuedNamedCurrentDensity_integrableOn_of_gaps (σ : ℂ) (N : ℕ) (f : SelectorFunctions)
    {r : ℝ} (hr : r ≠ 0) (τ lam : ℝ) (q : Fin N)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m) (ha : ContDiff ℝ ∞ f.a)
    {s : ℂ} (hs : s ≠ 0)
    (hW : ∀ θ ∈ angleBox N ∩ tsupport (namedSelectorDerivative f q),
      ∀ i, sourceW s (deformedPoint f r τ lam θ i) ∈ continuedRootDomain)
    (hY : ∀ θ ∈ angleBox N ∩ tsupport (namedSelectorDerivative f q),
      1-σ*coordinateProduct (deformedPoint f r τ lam θ) ≠ 0)
    (hZ : ∀ θ ∈ angleBox N ∩ tsupport (namedSelectorDerivative f q),
      1-σ*coordinateProduct (fun i => selectedContinuedRoot s (deformedPoint f r τ lam θ i)) ≠ 0) :
    IntegrableOn (signedContinuedNamedCurrentDensity σ f r τ lam s q) (angleBox N) := by
  let K := angleBox N ∩ tsupport (namedSelectorDerivative f q)
  have hK : IsCompact K := isCompact_Icc.inter_right (isClosed_tsupport _)
  have hc : ContinuousOn (signedContinuedNamedCurrentDensity σ f r τ lam s q) K := by
    intro θ hθ
    have hden := (signed_continuedContourDensity_analyticAt σ (p := (s,deformedPoint f r τ lam θ)) hs (deformedPoint_nonzero f hr τ lam θ)
      (hW θ hθ) (hY θ hθ) (hZ θ hθ)).continuousAt
    have hpoint : ContinuousAt (fun x => (s,deformedPoint f r τ lam x)) θ :=
      continuousAt_const.prodMk ((deformedPoint_continuous f r τ lam hp.continuous hm.continuous).continuousAt)
    have hweight : ContinuousAt (namedCurrentAngularWeight N f τ lam q) θ := (namedCurrentAngularWeight_continuous N f τ lam q hp hm ha).continuousAt
    have he : signedContinuedNamedCurrentDensity σ f r τ lam s q =
        (fun x => namedCurrentAngularWeight N f τ lam q x * signedContinuedContourDensity σ N (s,deformedPoint f r τ lam x)) :=
      funext (signed_continuedNamedCurrentDensity_weighted σ f r τ lam s q)
    rw [he]
    exact (hweight.mul (hden.comp (f := fun x => (s,deformedPoint f r τ lam x)) hpoint)).continuousWithinAt
  have hi := hc.integrableOn_compact (μ := volume) hK
  apply IntegrableOn.of_inter_support measurableSet_Icc
  apply hi.mono_set
  intro θ hθ
  refine ⟨hθ.1,subset_tsupport _ ?_⟩
  by_contra hz
  have he : namedSelectorDerivative f q θ=0 := by simpa only [Function.mem_support,not_not] using hz
  exact hθ.2 (by simp [signedContinuedNamedCurrentDensity,he])


theorem signed_continuedCurrentSlice_norm_le_onebody (σ : ℂ) (N : ℕ) (f : SelectorFunctions)
    {r : ℝ} (hr : r ≠ 0) (τ lam : ℝ)
    (hp : ContDiff ℝ ∞ f.p) (hm : ContDiff ℝ ∞ f.m) (ha : ContDiff ℝ ∞ f.a)
    {s : ℂ} (hs : s ≠ 0) {b η C eps A : ℝ}
    (hb : 0≤b) (hbT : b≤2*Real.pi) (hC : 0≤C) (heps : 0<eps) (hA : 0≤A)
    (hW : ∀ q, ∀ θ ∈ angleBox N ∩ tsupport (namedSelectorDerivative f q),
      ∀ i, sourceW s (deformedPoint f r τ lam θ i) ∈ continuedRootDomain)
    (hY : ∀ q, ∀ θ ∈ angleBox N ∩ tsupport (namedSelectorDerivative f q),
      1-σ*coordinateProduct (deformedPoint f r τ lam θ) ≠ 0)
    (hZ : ∀ q, ∀ θ ∈ angleBox N ∩ tsupport (namedSelectorDerivative f q),
      1-σ*coordinateProduct (fun i => selectedContinuedRoot s (deformedPoint f r τ lam θ i)) ≠ 0)
    (hbound : ∀ q, ∀ θ ∈ angleBox N ∩ tsupport (namedSelectorDerivative f q),
      ‖signedContinuedNamedCurrentDensity σ f r τ lam s q θ‖≤A*∏ i, selectedOneBodyBound b η C eps (θ i)) :
    ‖signedContinuedCurrentSlice σ N f r τ lam s‖≤
      (N:ℝ)*A*(4*C*Real.sqrt (2*Real.pi)+C*(2*Real.pi))^N := by
  have hterm (q : Fin N) : ‖signedContinuedNamedCurrentIntegral σ N f r τ lam q s‖≤
      A*(4*C*Real.sqrt (2*Real.pi)+C*(2*Real.pi))^N := by
    apply norm_angular_integral_le_onebody_product N hb hbT hC heps hA _
      (signed_continuedNamedCurrentDensity_integrableOn_of_gaps σ N f hr τ lam q hp hm ha hs (hW q) (hY q) (hZ q))
    intro θ hθ
    by_cases ht : θ ∈ tsupport (namedSelectorDerivative f q)
    · exact hbound q θ ⟨hθ,ht⟩
    · have hz := image_eq_zero_of_notMem_tsupport ht
      rw [signedContinuedNamedCurrentDensity,hz,Complex.ofReal_zero,mul_zero,zero_mul,norm_zero]
      exact mul_nonneg hA (Finset.prod_nonneg (fun _ _ => selectedOneBodyBound_nonneg hC))
  calc
    _ ≤ ∑ q : Fin N, ‖signedContinuedNamedCurrentIntegral σ N f r τ lam q s‖ := norm_sum_le _ _
    _ ≤ ∑ _q : Fin N, A*(4*C*Real.sqrt (2*Real.pi)+C*(2*Real.pi))^N :=
      Finset.sum_le_sum (fun q _ => hterm q)
    _ = _ := by simp [mul_assoc]

end
end IsingBulk.HT.Contour
