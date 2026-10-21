import IsingBulk.HT.Contour.SignedPiola
import IsingBulk.Tail.MixedActiveSourceGerm

/-! Literal signed mixed source factorization. The physical branch and compact
one-body measure, full coupled Jacobian and amplitude are unchanged. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Tail IsingBulk.Jets
open scoped BigOperators

theorem signed_mixed_pulledDensity_active_amplitude (ζ : ℂ) {N : ℕ}
    (J : Finset (Fin N)) (q : Fin N) (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hbranch : ∀ i∈J,Real.sin (θ i)<0)
    (hW : ∀ i,0<(sourceW s (deformedPoint f r τ lam θ i)).im) :
    signedPulledDensity ζ f r τ lam s θ=
      (N.factorial:ℂ)⁻¹*(2*(Real.pi:ℂ)*Complex.I)^(-(N:ℤ))*
        (angularJacobian f τ lam θ).det*mixedHybridVolume J f r τ lam s θ*
        mixedActiveRegularAmplitude J q s (fun i => mixedSourcePhase s (deformedPoint f r τ lam θ i))
          (deformedPoint f r τ lam θ) 0/
        ((1-ζ*coordinateProduct (fun i => globalRoot s (deformedPoint f r τ lam θ i)))*
          (1-ζ*coordinateProduct (deformedPoint f r τ lam θ))) := by
  rw [mixedActiveRegularAmplitude_source J q f hr τ lam s θ hbranch hW]
  have hb := mixed_source_onebody_product J f hr τ lam s θ hbranch (fun i _ => hW i)
  unfold signedPulledDensity signedCanceledDensity signedGlobalFactor
  calc
    _ = (N.factorial:ℂ)⁻¹*(2*(Real.pi:ℂ)*Complex.I)^(-(N:ℤ))*
        (angularJacobian f τ lam θ).det*
        ((coordinateProduct (fun i => globalRoot s (deformedPoint f r τ lam θ i)))⁻¹+
          (coordinateProduct (deformedPoint f r τ lam θ))⁻¹)/
        ((1-ζ*coordinateProduct (fun i => globalRoot s (deformedPoint f r τ lam θ i)))*
          (1-ζ*coordinateProduct (deformedPoint f r τ lam θ)))*
        canceledPairProduct (fun i => globalRoot s (deformedPoint f r τ lam θ i)) (deformedPoint f r τ lam θ)*
        ((∏ i,deformedPoint f r τ lam θ i)*(∏ i,residueFactor (globalRoot s (deformedPoint f r τ lam θ i)))) := by ring
    _ = _ := by rw [← hb]; ring

end
end IsingBulk.HT.Contour
