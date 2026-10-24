import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan

/-! The geometric objects in ANISO (1.1)--(1.5), (2.1)--(2.4).
The spectral set retains the unsquared equation and two real segment parameters.
No susceptibility, continuation, or maximality is part of these definitions. -/
namespace IsingBulk.Anisotropic

noncomputable section

def spectralS (z : ℂ) : ℂ := Complex.sinh z
def spectralT (lam : ℝ) (z : ℂ) : ℂ := Complex.sinh ((lam : ℂ) * z)
def spectralA (lam : ℝ) (z : ℂ) : ℂ := Complex.cosh z * Complex.cosh ((lam : ℂ) * z)
def spectralProduct (lam : ℝ) (z : ℂ) : ℂ := spectralS z * spectralT lam z

def spectralSet (lam : ℝ) : Set ℂ :=
  {z | ∃ u ∈ Set.Icc (-1 : ℝ) 1, ∃ v ∈ Set.Icc (-1 : ℝ) 1,
    spectralA lam z = spectralS z * (u : ℂ) + spectralT lam z * (v : ℂ)}

def sliceP (lam x : ℝ) : ℝ := Real.cosh x * Real.tanh (lam * x)
def sliceQ (lam x : ℝ) : ℝ := Real.cosh (lam * x) * Real.tanh x

def slicePInv (lam : ℝ) : ℝ → ℝ := Function.invFun (sliceP lam)
def sliceQInv (lam : ℝ) : ℝ → ℝ := Function.invFun (sliceQ lam)
def sliceY (lam : ℝ) : ℝ := Real.pi / (2 * max 1 lam)
def sliceH (lam y : ℝ) : ℝ :=
  min (slicePInv lam (Real.cos y)) (sliceQInv lam (Real.cos (lam * y)))
def sliceL (lam y : ℝ) : ℝ :=
  max (slicePInv lam |Real.cos y|) (sliceQInv lam |Real.cos (lam * y)|)
def omegaH (lam : ℝ) : Set ℂ := {z | |z.im| < sliceY lam ∧ |z.re| < sliceH lam z.im}
def omegaL (lam : ℝ) : Set ℂ := {z | sliceL lam z.im < z.re}

def geometryF1 (lam x y : ℝ) : ℝ :=
  Real.cosh (lam*x)^2 * Real.cos y^2 - Real.cosh x^2 * Real.sinh (lam*x)^2

def geometryF2 (lam x y : ℝ) : ℝ :=
  Real.cosh x^2 * Real.cos (lam*y)^2 - Real.sinh x^2 * Real.cosh (lam*x)^2

end
end IsingBulk.Anisotropic
