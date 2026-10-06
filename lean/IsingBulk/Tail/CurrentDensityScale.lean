import IsingBulk.Tail.ProtectedCompleteDensity

/-! Density envelope with the geometric gap scale independent of the real
homotopy parameter, so the original disk also includes lambda=0. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First
open scoped BigOperators
theorem continuedNamedCurrentDensity_scale_bound {N : ℕ} (f : SelectorFunctions)
    (r τ lam : ℝ) (s : ℂ) (q : Fin N) (θ : Fin N → ℝ)
    (w : Fin N → ℝ) {A P G κ J E B scale : ℝ}
    (hA : 0≤A) (hP : 0≤P) (hG : 0<G) (hscale : 0<scale)
    (hJ : 0≤J) (hE : 0≤E) (hB : 0≤B)
    (hnum : ‖(coordinateProduct (fun i => selectedContinuedRoot s (deformedPoint f r τ lam θ i)))⁻¹+
      (coordinateProduct (deformedPoint f r τ lam θ))⁻¹‖≤2*A^N)
    (hgap : G*scale^2≤‖(1-coordinateProduct (fun i => selectedContinuedRoot s (deformedPoint f r τ lam θ i)))*
      (1-coordinateProduct (deformedPoint f r τ lam θ))‖)
    (hpair : ‖canceledPairProduct (fun i => selectedContinuedRoot s (deformedPoint f r τ lam θ i))
      (deformedPoint f r τ lam θ)‖≤P^N*Real.exp (-κ*(N:ℝ)^2))
    (hw : ∀ i, 0≤w i)
    (hv : ∀ i, ‖residueFactor (selectedContinuedRoot s (deformedPoint f r τ lam θ i))‖≤w i)
    (hy : ∀ i, ‖deformedPoint f r τ lam θ i‖≤E)
    (hj : ‖(angularJacobian f τ lam θ).det‖≤J^N)
    (hm : ‖-2*Complex.I*(τ:ℂ)*(namedSelectorDerivative f q θ:ℂ)‖≤B) :
    ‖continuedNamedCurrentDensity f r τ lam s q θ‖≤
      ((N.factorial:ℝ)⁻¹*(2*B/G/scale^2)*((2*Real.pi)⁻¹*J*E*A*P)^N*
        Real.exp (-κ*(N:ℝ)^2))*(∏ i, w i) := by
  have hd := canceledReducedDensity_complete_bound _ _ w hA hP hG hscale hnum hgap hpair hw hv
  have hyp : ∏ i, ‖deformedPoint f r τ lam θ i‖≤E^N := by
    calc
      _ ≤ ∏ _i : Fin N, E := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hy i)
      _ = _ := by simp
  rw [continuedNamedCurrentDensity,norm_mul,continuedPulledDensity_norm]
  calc
    _ ≤ B*(((N.factorial:ℝ)⁻¹*(2*Real.pi)⁻¹^N)*J^N*E^N*
      ((2/G/scale^2)*(A*P)^N*Real.exp (-κ*(N:ℝ)^2)*(∏ i, w i))) := by gcongr
    _ = _ := by simp only [mul_pow]; ring

end
end IsingBulk.Tail
