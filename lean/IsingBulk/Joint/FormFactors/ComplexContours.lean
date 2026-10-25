import IsingBulk.Joint.Geometry.Definitions
import IsingBulk.Anisotropic.FormFactors.ContourAlgebra
import Mathlib.Analysis.Analytic.Basic

/-! Literal independent-coupling double contours, JOINT (3.6), (3.8).
The radius is selected solely from a geometric nonvanishing annulus, not from
analyticity of susceptibility. Existence of the annulus, contour independence, and convergence
are separate obligations: no such assertion is an axiom of this module.
The zero fallbacks make the definitions total and cannot certify any endpoint. -/
namespace IsingBulk.Joint.FormFactors
noncomputable section
open IsingBulk.Anisotropic.FormFactors IsingBulk.First
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def dispersion (K : Coupling) (x y : ℂ) : ℂ :=
  dispersionPolynomial (S K) (T K) (A K) x y

def ContourAnnulus (K : Coupling) (r : ℝ) : Prop :=
  0 < r ∧ r < 1 ∧ ∀ x y : ℂ,
    r ≤ ‖x‖ → ‖x‖ ≤ 1 → r ≤ ‖y‖ → ‖y‖ ≤ 1 → dispersion K x y ≠ 0

def contourRadius (K : Coupling) : ℝ :=
  if h : ∃ r, ContourAnnulus K r then Classical.choose h else 1/2

theorem contourRadius_spec {K : Coupling} (h : ∃ r, ContourAnnulus K r) :
    ContourAnnulus K (contourRadius K) := by
  simp only [contourRadius, dite_eq_left h]
  exact Classical.choose_spec h

def commonDensity {N : ℕ} (K : Coupling) (x y : Fin N → ℂ) : ℂ :=
  First.pairProduct x * First.pairProduct y * ∏ i, (dispersion K (x i) (y i))⁻¹

def fullDensity {N : ℕ} (K : Coupling) (x y : Fin N → ℂ) : ℂ :=
  ((1+coordinateProduct x)*(1+coordinateProduct y) /
    (coordinateProduct x*coordinateProduct y*(1-coordinateProduct x)*(1-coordinateProduct y))) *
    commonDensity K x y

def onsiteDensity {N : ℕ} (K : Coupling) (x y : Fin N → ℂ) : ℂ :=
  (coordinateProduct x*coordinateProduct y)⁻¹ * commonDensity K x y

def offsiteDensity {N : ℕ} (K : Coupling) (x y : Fin N → ℂ) : ℂ :=
  ((coordinateProduct x)⁻¹+(coordinateProduct y)⁻¹) /
    ((1-coordinateProduct x)*(1-coordinateProduct y)) * commonDensity K x y

/-- F_N is the unscaled full coefficient: no sqrt(p) is used here. -/
def unscaledFullCoefficientAtRadius (N : ℕ) (r : ℝ) (K : Coupling) : ℂ :=
  (N.factorial:ℂ)⁻¹ * multiCircleIntegral r N (fun y =>
    multiCircleIntegral r N (fun x => fullDensity K x y))

def unscaledFullCoefficient (N : ℕ) (K : Coupling) : ℂ :=
  unscaledFullCoefficientAtRadius N (contourRadius K) K

/-- Exact onsite/offsite density split, with no omitted axes. -/
theorem fullDensity_eq_onsite_add_twice {N : ℕ} (K : Coupling)
    (x y : Fin N → ℂ) (hx : coordinateProduct x ≠ 0) (hy : coordinateProduct y ≠ 0)
    (hx1 : 1-coordinateProduct x ≠ 0) (hy1 : 1-coordinateProduct y ≠ 0) :
    fullDensity K x y = onsiteDensity K x y + 2*offsiteDensity K x y := by
  unfold fullDensity onsiteDensity offsiteDensity
  rw [full_site_multiplier _ _ hx hy hx1 hy1]
  simp only [one_div]
  ring
end
end IsingBulk.Joint.FormFactors
