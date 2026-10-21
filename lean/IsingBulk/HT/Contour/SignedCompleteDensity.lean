import IsingBulk.HT.Contour.SignedDensityEstimate
import IsingBulk.Tail.ProtectedCompleteDensity

/-! Signed complete-pair-to-current density transfer. All premises here
are transparent factor bounds; the constructed source supplies them below. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Tail
open scoped BigOperators

theorem signed_canceledReducedDensity_complete_bound (σ : ℂ) {N : ℕ} (z y : Fin N → ℂ)
    (w : Fin N → ℝ) {A P G lam κ : ℝ}
    (hA : 0≤A) (hP : 0≤P) (hG : 0<G) (hlam : 0<lam)
    (hnum : ‖(coordinateProduct z)⁻¹+(coordinateProduct y)⁻¹‖≤2*A^N)
    (hgap : G*lam^2≤‖(1-σ*coordinateProduct z)*(1-σ*coordinateProduct y)‖)
    (hpair : ‖canceledPairProduct z y‖≤P^N*Real.exp (-κ*(N:ℝ)^2))
    (_hw : ∀ i, 0≤w i) (hv : ∀ i, ‖residueFactor (z i)‖≤w i) :
    ‖signedCanceledDensity σ z y‖≤
      (2/G/lam^2)*(A*P)^N*Real.exp (-κ*(N:ℝ)^2)*(∏ i, w i) := by
  have hglob : ‖((coordinateProduct z)⁻¹+(coordinateProduct y)⁻¹)/
      ((1-σ*coordinateProduct z)*(1-σ*coordinateProduct y))‖≤2*A^N/(G*lam^2) := by
    rw [norm_div]
    exact div_le_div₀ (by positivity) hnum (by positivity) hgap
  have hvprod : ∏ i, ‖residueFactor (z i)‖≤∏ i, w i :=
    Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hv i)
  calc
    _ ≤ (2*A^N/(G*lam^2))*(P^N*Real.exp (-κ*(N:ℝ)^2))*(∏ i, w i) := by
      simp only [signedCanceledDensity,signedGlobalFactor,norm_mul,norm_prod]
      gcongr
    _ = _ := by rw [mul_pow]; field_simp

theorem signed_continuedNamedCurrentDensity_complete_bound (σ : ℂ) {N : ℕ} (f : SelectorFunctions)
    (r τ lam : ℝ) (s : ℂ) (q : Fin N) (θ : Fin N → ℝ)
    (w : Fin N → ℝ) {A P G κ J E B : ℝ}
    (hA : 0≤A) (hP : 0≤P) (hG : 0<G) (hlam : 0<lam)
    (hJ : 0≤J) (hE : 0≤E) (hB : 0≤B)
    (hnum : ‖(coordinateProduct (fun i => selectedContinuedRoot s (deformedPoint f r τ lam θ i)))⁻¹+
      (coordinateProduct (deformedPoint f r τ lam θ))⁻¹‖≤2*A^N)
    (hgap : G*lam^2≤‖(1-σ*coordinateProduct (fun i => selectedContinuedRoot s (deformedPoint f r τ lam θ i)))*
      (1-σ*coordinateProduct (deformedPoint f r τ lam θ))‖)
    (hpair : ‖canceledPairProduct (fun i => selectedContinuedRoot s (deformedPoint f r τ lam θ i))
      (deformedPoint f r τ lam θ)‖≤P^N*Real.exp (-κ*(N:ℝ)^2))
    (hw : ∀ i, 0≤w i)
    (hv : ∀ i, ‖residueFactor (selectedContinuedRoot s (deformedPoint f r τ lam θ i))‖≤w i)
    (hy : ∀ i, ‖deformedPoint f r τ lam θ i‖≤E)
    (hj : ‖(angularJacobian f τ lam θ).det‖≤J^N)
    (hm : ‖-2*Complex.I*(τ:ℂ)*(namedSelectorDerivative f q θ:ℂ)‖≤B) :
    ‖signedContinuedNamedCurrentDensity σ f r τ lam s q θ‖≤
      ((N.factorial:ℝ)⁻¹*(2*B/G/lam^2)*((2*Real.pi)⁻¹*J*E*A*P)^N*
        Real.exp (-κ*(N:ℝ)^2))*(∏ i, w i) := by
  have hd := signed_canceledReducedDensity_complete_bound σ _ _ w hA hP hG hlam hnum hgap hpair hw hv
  have hyp : ∏ i, ‖deformedPoint f r τ lam θ i‖≤E^N := by
    calc
      _ ≤ ∏ _i : Fin N, E := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hy i)
      _ = _ := by simp
  rw [signedContinuedNamedCurrentDensity,norm_mul,signed_continuedPulledDensity_norm σ]
  calc
    _ ≤ B*(((N.factorial:ℝ)⁻¹*(2*Real.pi)⁻¹^N)*J^N*E^N*
      ((2/G/lam^2)*(A*P)^N*Real.exp (-κ*(N:ℝ)^2)*(∏ i, w i))) := by gcongr
    _ = _ := by simp only [mul_pow]; ring

end
end IsingBulk.HT.Contour
