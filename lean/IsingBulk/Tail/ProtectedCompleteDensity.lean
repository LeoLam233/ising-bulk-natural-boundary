import IsingBulk.Tail.ProtectedActualOneBody
import IsingBulk.Tail.CurrentGlobalEnvelope
import IsingBulk.Tail.CurrentMultiplierBounds
import IsingBulk.Tail.ProtectedAngularEnvelope
import IsingBulk.Tail.SelectedFDensityEstimate

/-! Transparent complete-pair-to-density transfers for protected currents.
The full canceled-pair bound is an explicit premise here, not a source-node
conclusion or a new external input. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First
open scoped BigOperators

theorem canceledReducedDensity_complete_bound {N : ℕ} (z y : Fin N → ℂ)
    (w : Fin N → ℝ) {A P G lam κ : ℝ}
    (hA : 0≤A) (hP : 0≤P) (hG : 0<G) (hlam : 0<lam)
    (hnum : ‖(coordinateProduct z)⁻¹+(coordinateProduct y)⁻¹‖≤2*A^N)
    (hgap : G*lam^2≤‖(1-coordinateProduct z)*(1-coordinateProduct y)‖)
    (hpair : ‖canceledPairProduct z y‖≤P^N*Real.exp (-κ*(N:ℝ)^2))
    (_hw : ∀ i, 0≤w i) (hv : ∀ i, ‖residueFactor (z i)‖≤w i) :
    ‖canceledReducedDensity z y‖≤
      (2/G/lam^2)*(A*P)^N*Real.exp (-κ*(N:ℝ)^2)*(∏ i, w i) := by
  have hglob : ‖((coordinateProduct z)⁻¹+(coordinateProduct y)⁻¹)/
      ((1-coordinateProduct z)*(1-coordinateProduct y))‖≤2*A^N/(G*lam^2) := by
    rw [norm_div]
    exact div_le_div₀ (by positivity) hnum (by positivity) hgap
  have hvprod : ∏ i, ‖residueFactor (z i)‖≤∏ i, w i :=
    Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hv i)
  calc
    _ ≤ (2*A^N/(G*lam^2))*(P^N*Real.exp (-κ*(N:ℝ)^2))*(∏ i, w i) := by
      simp only [canceledReducedDensity,norm_mul,norm_prod]
      gcongr
    _ = _ := by rw [mul_pow]; field_simp

theorem continuedNamedCurrentDensity_complete_bound {N : ℕ} (f : SelectorFunctions)
    (r τ lam : ℝ) (s : ℂ) (q : Fin N) (θ : Fin N → ℝ)
    (w : Fin N → ℝ) {A P G κ J E B : ℝ}
    (hA : 0≤A) (hP : 0≤P) (hG : 0<G) (hlam : 0<lam)
    (hJ : 0≤J) (hE : 0≤E) (hB : 0≤B)
    (hnum : ‖(coordinateProduct (fun i => selectedContinuedRoot s (deformedPoint f r τ lam θ i)))⁻¹+
      (coordinateProduct (deformedPoint f r τ lam θ))⁻¹‖≤2*A^N)
    (hgap : G*lam^2≤‖(1-coordinateProduct (fun i => selectedContinuedRoot s (deformedPoint f r τ lam θ i)))*
      (1-coordinateProduct (deformedPoint f r τ lam θ))‖)
    (hpair : ‖canceledPairProduct (fun i => selectedContinuedRoot s (deformedPoint f r τ lam θ i))
      (deformedPoint f r τ lam θ)‖≤P^N*Real.exp (-κ*(N:ℝ)^2))
    (hw : ∀ i, 0≤w i)
    (hv : ∀ i, ‖residueFactor (selectedContinuedRoot s (deformedPoint f r τ lam θ i))‖≤w i)
    (hy : ∀ i, ‖deformedPoint f r τ lam θ i‖≤E)
    (hj : ‖(angularJacobian f τ lam θ).det‖≤J^N)
    (hm : ‖-2*Complex.I*(τ:ℂ)*(namedSelectorDerivative f q θ:ℂ)‖≤B) :
    ‖continuedNamedCurrentDensity f r τ lam s q θ‖≤
      ((N.factorial:ℝ)⁻¹*(2*B/G/lam^2)*((2*Real.pi)⁻¹*J*E*A*P)^N*
        Real.exp (-κ*(N:ℝ)^2))*(∏ i, w i) := by
  have hd := canceledReducedDensity_complete_bound _ _ w hA hP hG hlam hnum hgap hpair hw hv
  have hyp : ∏ i, ‖deformedPoint f r τ lam θ i‖≤E^N := by
    calc
      _ ≤ ∏ _i : Fin N, E := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hy i)
      _ = _ := by simp
  rw [continuedNamedCurrentDensity,norm_mul,continuedPulledDensity_norm]
  calc
    _ ≤ B*(((N.factorial:ℝ)⁻¹*(2*Real.pi)⁻¹^N)*J^N*E^N*
      ((2/G/lam^2)*(A*P)^N*Real.exp (-κ*(N:ℝ)^2)*(∏ i, w i))) := by gcongr
    _ = _ := by simp only [mul_pow]; ring

end
end IsingBulk.Tail
