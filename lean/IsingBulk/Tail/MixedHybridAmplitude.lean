import IsingBulk.Tail.MixedHybridDensity
import IsingBulk.Tail.MixedBranchIdentification

/-! Exact source measure in mixed coordinates. The full occupancy-coupled
angular determinant and the factorial normalization remain literal. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.First IsingBulk.Branch IsingBulk.Jets
open scoped BigOperators

def mixedSourceOneBody {N : ℕ} (J : Finset (Fin N)) (f : SelectorFunctions)
    (r τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) (i : Fin N) : ℂ :=
  if i∈J then (2*(Real.pi:ℂ))*microRegularOneBody s (mixedContourPhase f r τ lam s θ i)
  else deformedPoint f r τ lam θ i*residueFactor (globalRoot s (deformedPoint f r τ lam θ i))

def mixedSourceAmplitude {N : ℕ} (J : Finset (Fin N)) (f : SelectorFunctions)
    (r τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  let y := deformedPoint f r τ lam θ
  let z := fun i => globalRoot s (y i)
  (N.factorial:ℂ)⁻¹*(2*(Real.pi:ℂ)*Complex.I)^(-(N:ℤ))*
    (angularJacobian f τ lam θ).det*
    ((coordinateProduct z)⁻¹+(coordinateProduct y)⁻¹)/
      ((1-coordinateProduct z)*(1-coordinateProduct y))*
    canceledPairProduct z y*∏ i,mixedSourceOneBody J f r τ lam s θ i

theorem mixed_source_onebody_product {N : ℕ} (J : Finset (Fin N)) (f : SelectorFunctions)
    {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hsin : ∀ i∈J,Real.sin (θ i)<0)
    (hW : ∀ i∈J,0<(sourceW s (deformedPoint f r τ lam θ i)).im) :
    mixedHybridVolume J f r τ lam s θ*(∏ i,mixedSourceOneBody J f r τ lam s θ i)=
      (∏ i,deformedPoint f r τ lam θ i)*(∏ i,residueFactor (globalRoot s (deformedPoint f r τ lam θ i))) := by
  have hv : mixedHybridVolume J f r τ lam s θ=
      ∏ i,if i∈J then mixedSourceSlope s (deformedPoint f r τ lam θ i) else 1 := by
    simp [mixedHybridVolume]
  rw [hv,← Finset.prod_mul_distrib,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i∈J
  · simp only [hi,ite_true,mixedSourceOneBody]
    have hh := mixed_actual_regular_onebody f hr τ lam s θ i (hsin i hi) (hW i hi)
    have hpi : (2*(Real.pi:ℂ))≠0 := mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
    calc
      _ = (mixedSourceSlope s (deformedPoint f r τ lam θ i)*
          microRegularOneBody s (mixedContourPhase f r τ lam s θ i))*(2*(Real.pi:ℂ)) := by ring
      _ = _ := by rw [hh,div_mul_cancel₀ _ hpi]; ring
  · simp [hi,mixedSourceOneBody]

/-- Literal source density, not an abstract amplitude certificate. -/
theorem mixed_pulledDensity_factorization {N : ℕ} (J : Finset (Fin N)) (f : SelectorFunctions)
    {r : ℝ} (hr : 0<r) (τ lam : ℝ) (s : ℂ) (θ : Fin N → ℝ)
    (hsin : ∀ i∈J,Real.sin (θ i)<0)
    (hW : ∀ i∈J,0<(sourceW s (deformedPoint f r τ lam θ i)).im) :
    pulledDensity f r τ lam s θ=mixedHybridVolume J f r τ lam s θ*mixedSourceAmplitude J f r τ lam s θ := by
  have hb := mixed_source_onebody_product J f hr τ lam s θ hsin hW
  unfold pulledDensity canceledReducedDensity mixedSourceAmplitude
  dsimp only
  calc
    _ = (N.factorial:ℂ)⁻¹*(2*(Real.pi:ℂ)*Complex.I)^(-(N:ℤ))*
        (angularJacobian f τ lam θ).det*
        ((coordinateProduct (fun i => globalRoot s (deformedPoint f r τ lam θ i)))⁻¹+
          (coordinateProduct (deformedPoint f r τ lam θ))⁻¹)/
        ((1-coordinateProduct (fun i => globalRoot s (deformedPoint f r τ lam θ i)))*
          (1-coordinateProduct (deformedPoint f r τ lam θ)))*
        canceledPairProduct (fun i => globalRoot s (deformedPoint f r τ lam θ i)) (deformedPoint f r τ lam θ)*
        ((∏ i,deformedPoint f r τ lam θ i)*(∏ i,residueFactor (globalRoot s (deformedPoint f r τ lam θ i)))) := by ring
    _ = _ := by rw [← hb]; ring

end
end IsingBulk.Tail
