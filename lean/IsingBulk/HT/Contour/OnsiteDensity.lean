import IsingBulk.HT.Final.OnsiteResidue
import IsingBulk.HT.Contour.SignedKernel

/-! Literal onsite reduced source, complete contour and named current.
The outside factorial, coupled angular determinant and one-body residues
are retained; the global factor is exactly (ZY) inverse, without poles. -/
namespace IsingBulk.HT.Contour
noncomputable section
open IsingBulk.First IsingBulk.Tail MeasureTheory Set
open scoped BigOperators Topology ContDiff

/-- The collision-regular reduced onsite density on the actual root sheet. -/
def onsiteCanceledDensity {N : ℕ} (z y : Fin N → ℂ) : ℂ :=
  (coordinateProduct z*coordinateProduct y)⁻¹*canceledPairProduct z y*
    ∏ i,residueFactor (z i)

def onsiteLogDensity (N : ℕ) (s : ℂ) (ℓ : Fin N → ℂ) : ℂ :=
  (N.factorial:ℂ)⁻¹*(2*(Real.pi:ℂ)*Complex.I)^(-(N:ℤ))*
    (∏ i, Complex.exp (ℓ i))*
    onsiteCanceledDensity (fun i => globalRoot s (Complex.exp (ℓ i)))
      (fun i => Complex.exp (ℓ i))

def onsitePulledDensity {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ)
    (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  (N.factorial:ℂ)⁻¹*(2*(Real.pi:ℂ)*Complex.I)^(-(N:ℤ))*
    (angularJacobian f τ lam θ).det*(∏ i, deformedPoint f r τ lam θ i)*
    onsiteCanceledDensity (fun i => globalRoot s (deformedPoint f r τ lam θ i))
      (deformedPoint f r τ lam θ)

def onsiteHomotopyFlux {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ)
    (s : ℂ) (θ : Fin N → ℝ) (q : Fin N) : ℂ :=
  onsiteLogDensity N s (logContour f r τ lam θ)*
    ((angularJacobian f τ lam θ).updateCol q (complexShift f τ θ)).det

def onsiteSelectedIntegral (N : ℕ) (f : SelectorFunctions) (r τ : ℝ)
    (s : ℂ) : ℂ :=
  ∫ θ in angleBox N, ((1-angularSelector f θ:ℝ):ℂ)*onsitePulledDensity f r τ 1 s θ

def onsiteOriginalLowerIntegral (N : ℕ) (f : SelectorFunctions) (r τ : ℝ)
    (s : ℂ) : ℂ :=
  ∫ θ in angleBox N, (angularSelector f θ:ℂ)*onsitePulledDensity f r τ 0 s θ

def onsiteNamedCurrentDensity {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ)
    (s : ℂ) (q : Fin N) (θ : Fin N → ℝ) : ℂ :=
  -2*Complex.I*(τ:ℂ)*(namedSelectorDerivative f q θ:ℂ)*onsitePulledDensity f r τ lam s θ

def onsiteCurrentIntegral (N : ℕ) (f : SelectorFunctions) (r τ : ℝ)
    (s : ℂ) : ℂ :=
  ∫ lam : ℝ in 0..1, ∑ q : Fin N, ∫ θ in angleBox N,
    onsiteNamedCurrentDensity f r τ lam s q θ

def onsiteSourceIntegral (N : ℕ) (r : ℝ) (s : ℂ) : ℂ :=
  ∫ θ in angleBox N, (N.factorial:ℂ)⁻¹*angleProductJacobian r θ*
    onsiteCanceledDensity (fun i => globalRoot s (anglePoint r (θ i))) (angleTuple r θ)

def onsiteHomotopyTotal (N : ℕ) (f : SelectorFunctions) (r τ lam : ℝ)
    (s : ℂ) : ℂ := ∫ θ in angleBox N, onsitePulledDensity f r τ lam s θ

def onsiteHomotopyLower (N : ℕ) (f : SelectorFunctions) (r τ lam : ℝ)
    (s : ℂ) : ℂ :=
  ∫ θ in angleBox N, (angularSelector f θ:ℂ)*onsitePulledDensity f r τ lam s θ


end
end IsingBulk.HT.Contour
