import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Algebra.BigOperators.Fin

/-! Actual normalized finite contour objects for FIRST. The radius is an explicit
fixed parameter. In particular it is never silently differentiated with s. -/
namespace IsingBulk.First
noncomputable section
open scoped BigOperators
open Complex MeasureTheory Set

/-- The source temperature trace. -/
def sourceS (s : ℂ) : ℂ := s + s⁻¹

/-- The double-contour dispersion denominator, in source variable order. -/
def dispersion (x y s : ℂ) : ℂ := sourceS s - (x + x⁻¹) / 2 - (y + y⁻¹) / 2

def coordinateProduct {N : ℕ} (x : Fin N → ℂ) : ℂ := ∏ i, x i

def pairKernel (a b : ℂ) : ℂ := (a - b) / (1 - a * b)

def pairProduct {N : ℕ} (x : Fin N → ℂ) : ℂ :=
  ∏ i, ∏ j ∈ Finset.univ.filter (fun j => i < j), pairKernel (x i) (x j)

def commonDensity {N : ℕ} (s : ℂ) (x y : Fin N → ℂ) : ℂ :=
  pairProduct x * pairProduct y * ∏ i, (dispersion (x i) (y i) s)⁻¹

def doubleDensity {N : ℕ} (s : ℂ) (x y : Fin N → ℂ) : ℂ :=
  (coordinateProduct x)⁻¹ + (coordinateProduct y)⁻¹ |> fun a =>
    a / ((1 - coordinateProduct x) * (1 - coordinateProduct y)) * commonDensity s x y

def onsiteDensity {N : ℕ} (s : ℂ) (x y : Fin N → ℂ) : ℂ :=
  (coordinateProduct x * coordinateProduct y)⁻¹ * commonDensity s x y

def standardDensity {N : ℕ} (s : ℂ) (x y : Fin N → ℂ) : ℂ :=
  (1 + (coordinateProduct x)⁻¹) * (1 + (coordinateProduct y)⁻¹) /
    ((1 - coordinateProduct x) * (1 - coordinateProduct y)) * commonDensity s x y

def residueFactor (z : ℂ) : ℂ := 2 * z ^ 2 / (1 - z ^ 2)

def reducedDensity {N : ℕ} (z y : Fin N → ℂ) : ℂ :=
  ((coordinateProduct z)⁻¹ + (coordinateProduct y)⁻¹) /
    ((1 - coordinateProduct z) * (1 - coordinateProduct y)) *
    pairProduct z * pairProduct y * ∏ i, residueFactor (z i)

/-- A positively oriented circle with precisely one source normalization. -/
def normalizedCircleIntegral (r : ℝ) (f : ℂ → ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * circleIntegral f 0 r

/-- Genuine iterated contour integrals, integrating the first coordinate first. -/
def multiCircleIntegral (r : ℝ) : (N : ℕ) → ((Fin N → ℂ) → ℂ) → ℂ
  | 0, f => f Fin.elim0
  | n + 1, f => multiCircleIntegral r n (fun x =>
      normalizedCircleIntegral r (fun z => f (Fin.cons z x)))

/-- The exact offsite form factor at a fixed admissible radius. -/
def doubleFormFactor (N : ℕ) (r : ℝ) (s : ℂ) : ℂ :=
  (N.factorial : ℂ)⁻¹ * multiCircleIntegral r N (fun y =>
    multiCircleIntegral r N (fun x => doubleDensity s x y))

/-- The reduced normalized integral for a specified root function. -/
def reducedFormFactor (N : ℕ) (r : ℝ) (z : ℂ → ℂ) : ℂ :=
  (N.factorial : ℂ)⁻¹ * multiCircleIntegral r N (fun y =>
    reducedDensity (fun i => z (y i)) y)

/-- Admissibility records source algebra and geometric domains only. -/
structure ResidueAdmissible {N : ℕ} (r : ℝ) (s : ℂ) (y z : Fin N → ℂ) : Prop where
  radius_pos : 0 < r
  radius_lt_one : r < 1
  y_on_circle : ∀ i, ‖y i‖ = r
  root_quadratic : ∀ i, (z i)^2 - (2 * sourceS s - y i - (y i)⁻¹) * z i + 1 = 0
  root_inside : ∀ i, ‖z i‖ < r

/-- The closed polydisk and distinguished boundary retain the actual radius. -/
def closedPolydisk (N : ℕ) (r : ℝ) : Set (Fin N → ℂ) := {x | ∀ i, ‖x i‖ ≤ r}
def productCircle (N : ℕ) (r : ℝ) : Set (Fin N → ℂ) := {x | ∀ i, ‖x i‖ = r}

end
end IsingBulk.First
