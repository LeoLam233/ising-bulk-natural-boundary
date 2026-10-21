import IsingBulk.HT.Contour.OnsiteDensity
import IsingBulk.Tail.MixedHybridAmplitude
import IsingBulk.HT.Lie.OnsiteTransport

/-! Literal onsite top form in the genuine mixed chart. All inverse products,
complete pairs, the coupled determinant and the outside factorial survive. -/
namespace IsingBulk.HT.Lie
noncomputable section
open IsingBulk.First IsingBulk.Tail IsingBulk.HT.Contour
open scoped BigOperators

def onsiteHybridAmplitude {N : ℕ} (J : Finset (Fin N)) (f : SelectorFunctions)
    (r τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  let y := deformedPoint f r τ lam θ
  let z := fun i => globalRoot s (y i)
  (N.factorial:ℂ)⁻¹*(2*(Real.pi:ℂ)*Complex.I)^(-(N:ℤ))*
    (angularJacobian f τ lam θ).det*
    (coordinateProduct z*coordinateProduct y)⁻¹*
    canceledPairProduct z y*∏ i,mixedSourceOneBody J f r τ lam s θ i

/-- Exact factorization, including configurations where complete pairs
vanish. No division by a Vandermonde factor is used. -/
theorem onsite_pulled_density_hybrid_factorization {N : ℕ}
    (J : Finset (Fin N)) (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hsin : ∀ i∈J,Real.sin (θ i)<0)
    (hW : ∀ i∈J,0<(sourceW s (deformedPoint f r τ lam θ i)).im) :
    onsitePulledDensity f r τ lam s θ =
      mixedHybridVolume J f r τ lam s θ*onsiteHybridAmplitude J f r τ lam s θ := by
  have hb := mixed_source_onebody_product J f hr τ lam s θ hsin hW
  unfold onsitePulledDensity onsiteCanceledDensity onsiteHybridAmplitude
  dsimp only
  calc
    _ = (N.factorial:ℂ)⁻¹*(2*(Real.pi:ℂ)*Complex.I)^(-(N:ℤ))*
        (angularJacobian f τ lam θ).det*
        (coordinateProduct (fun i => globalRoot s (deformedPoint f r τ lam θ i))*
          coordinateProduct (deformedPoint f r τ lam θ))⁻¹*
        canceledPairProduct (fun i => globalRoot s (deformedPoint f r τ lam θ i))
          (deformedPoint f r τ lam θ)*
        ((∏ i,deformedPoint f r τ lam θ i)*
          (∏ i,residueFactor (globalRoot s (deformedPoint f r τ lam θ i)))) := by ring
    _ = _ := by rw [← hb]; ring

/-- The original K and every named current use the same no-product-pole
regularization, with their actual real multipliers. -/
theorem onsite_weighted_hybrid_factorization {N : ℕ}
    (J : Finset (Fin N)) (f : SelectorFunctions) {r : ℝ} (hr : 0<r)
    (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (w : (Fin N → ℝ) → ℂ)
    (hsin : ∀ i∈J,Real.sin (θ i)<0)
    (hW : ∀ i∈J,0<(sourceW s (deformedPoint f r τ lam θ i)).im) :
    w θ*onsitePulledDensity f r τ lam s θ =
      mixedHybridVolume J f r τ lam s θ*(w θ*onsiteHybridAmplitude J f r τ lam s θ) := by
  rw [onsite_pulled_density_hybrid_factorization J f hr τ lam s θ hsin hW]
  ring

end
end IsingBulk.HT.Lie
