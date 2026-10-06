import IsingBulk.Tail.SelectorGeometry
import IsingBulk.First.GlobalResidueRoot
import IsingBulk.First.AngularFubini

/-! Literal coupled angular contour and its fixed-weight three pieces.
Definitions do not assert deformation invariance or any tail estimate. -/
namespace IsingBulk.Tail
noncomputable section
open scoped BigOperators
open IsingBulk.First MeasureTheory

structure SelectorFunctions where
  p : ℝ → ℝ
  m : ℝ → ℝ
  a : ℝ → ℝ

/-- The radius is a separate fixed parameter, not a function of the temperature. -/
def deformedPoint {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ)
    (θ : Fin N → ℝ) (i : Fin N) : ℂ :=
  (r:ℂ) * Complex.exp (Complex.I*(θ i:ℂ) +
    (lam*retractionShift τ (fun j => f.p (θ j)) (fun j => f.m (θ j)) i : ℝ))

def angularJacobian {N : ℕ} (f : SelectorFunctions) (τ lam : ℝ)
    (θ : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  retractionJacobian lam τ (fun i => f.p (θ i)) (fun i => f.m (θ i))
    (fun i => deriv f.p (θ i)) (fun i => deriv f.m (θ i))

/-- Complete source pair after cancellation, valid even on y reciprocity. -/
def canceledPair (yi yj zi zj : ℂ) : ℂ :=
  -(yi-yj)^2*zi*zj/(yi*yj*(1-zi*zj)^2)

def canceledPairProduct {N : ℕ} (z y : Fin N → ℂ) : ℂ :=
  ∏ i, ∏ j ∈ Finset.univ.filter (fun j => i<j), canceledPair (y i) (y j) (z i) (z j)

def canceledReducedDensity {N : ℕ} (z y : Fin N → ℂ) : ℂ :=
  ((coordinateProduct z)⁻¹+(coordinateProduct y)⁻¹)/
    ((1-coordinateProduct z)*(1-coordinateProduct y))*
    canceledPairProduct z y*∏ i, residueFactor (z i)

def pulledDensity {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ)
    (s : ℂ) (θ : Fin N → ℝ) : ℂ :=
  (N.factorial:ℂ)⁻¹ * (2*(Real.pi:ℂ)*Complex.I)^(- (N:ℤ)) *
    (angularJacobian f τ lam θ).det *
    (∏ i, deformedPoint f r τ lam θ i) *
    canceledReducedDensity (fun i => globalRoot s (deformedPoint f r τ lam θ i))
      (deformedPoint f r τ lam θ)

def angularSelector {N : ℕ} (f : SelectorFunctions) (θ : Fin N → ℝ) : ℝ :=
  selectorWeight (fun i => f.a (θ i))

def selectedIntegral (N : ℕ) (f : SelectorFunctions) (r τ : ℝ) (s : ℂ) : ℂ :=
  ∫ θ in angleBox N, ((1-angularSelector f θ:ℝ):ℂ)*pulledDensity f r τ 1 s θ

def originalLowerIntegral (N : ℕ) (f : SelectorFunctions) (r τ : ℝ) (s : ℂ) : ℂ :=
  ∫ θ in angleBox N, (angularSelector f θ:ℂ)*pulledDensity f r τ 0 s θ

def namedSelectorDerivative {N : ℕ} (f : SelectorFunctions) (q : Fin N)
    (θ : Fin N → ℝ) : ℝ :=
  -deriv f.a (θ q) * ∏ i ∈ Finset.univ.erase q, (1-f.a (θ i))

def namedCurrentDensity {N : ℕ} (f : SelectorFunctions) (r τ lam : ℝ)
    (s : ℂ) (q : Fin N) (θ : Fin N → ℝ) : ℂ :=
  -2*Complex.I*(τ:ℂ)*(namedSelectorDerivative f q θ:ℂ)*pulledDensity f r τ lam s θ

def currentIntegral (N : ℕ) (f : SelectorFunctions) (r τ : ℝ) (s : ℂ) : ℂ :=
  ∫ lam : ℝ in 0..1, ∑ q : Fin N, ∫ θ in angleBox N,
    namedCurrentDensity f r τ lam s q θ

end
end IsingBulk.Tail
