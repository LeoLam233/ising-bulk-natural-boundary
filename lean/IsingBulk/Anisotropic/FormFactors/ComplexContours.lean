import IsingBulk.Anisotropic.Geometry.Definitions
import IsingBulk.Anisotropic.FormFactors.ContourAlgebra
import Mathlib.Analysis.Analytic.Basic

/-! Literal complex full sums in ANISO (1.9)--(1.16).
The radius is selected solely from a geometric nonvanishing annulus, not from
analyticity of susceptibility. Existence of the annulus and of the normalized
fourth-root branches, their uniqueness, contour independence, and convergence
are separate obligations: no such assertion is an axiom of this module.
The zero fallbacks make the definitions total and cannot certify any endpoint. -/
namespace IsingBulk.Anisotropic.FormFactors
noncomputable section
open IsingBulk.First
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def sliceDispersion (lam : ℝ) (z x y : ℂ) : ℂ :=
  dispersionPolynomial (spectralS z) (spectralT lam z) (spectralA lam z) x y

def ContourAnnulus (lam : ℝ) (z : ℂ) (r : ℝ) : Prop :=
  0 < r ∧ r < 1 ∧ ∀ x y : ℂ,
    r ≤ ‖x‖ → ‖x‖ ≤ 1 → r ≤ ‖y‖ → ‖y‖ ≤ 1 → sliceDispersion lam z x y ≠ 0

def contourRadius (lam : ℝ) (z : ℂ) : ℝ :=
  if h : ∃ r, ContourAnnulus lam z r then Classical.choose h else 1/2

theorem contourRadius_spec {lam : ℝ} {z : ℂ} (h : ∃ r, ContourAnnulus lam z r) :
    ContourAnnulus lam z (contourRadius lam z) := by
  simp only [contourRadius, dite_eq_left h]
  exact Classical.choose_spec h

def commonDensity {N : ℕ} (lam : ℝ) (z : ℂ) (x y : Fin N → ℂ) : ℂ :=
  First.pairProduct x * First.pairProduct y * ∏ i, (sliceDispersion lam z (x i) (y i))⁻¹

def fullDensity {N : ℕ} (lam : ℝ) (z : ℂ) (x y : Fin N → ℂ) : ℂ :=
  ((1+coordinateProduct x)*(1+coordinateProduct y) /
    (coordinateProduct x*coordinateProduct y*(1-coordinateProduct x)*(1-coordinateProduct y))) *
    commonDensity lam z x y

def onsiteDensity {N : ℕ} (lam : ℝ) (z : ℂ) (x y : Fin N → ℂ) : ℂ :=
  (coordinateProduct x*coordinateProduct y)⁻¹ * commonDensity lam z x y

def offsiteDensity {N : ℕ} (lam : ℝ) (z : ℂ) (x y : Fin N → ℂ) : ℂ :=
  ((coordinateProduct x)⁻¹+(coordinateProduct y)⁻¹) /
    ((1-coordinateProduct x)*(1-coordinateProduct y)) * commonDensity lam z x y

/-- F_N is the unscaled full coefficient: no sqrt(p) is used here. -/
def unscaledFullCoefficientAtRadius (N : ℕ) (r lam : ℝ) (z : ℂ) : ℂ :=
  (N.factorial:ℂ)⁻¹ * multiCircleIntegral r N (fun y =>
    multiCircleIntegral r N (fun x => fullDensity lam z x y))

def unscaledFullCoefficient (N : ℕ) (lam : ℝ) (z : ℂ) : ℂ :=
  unscaledFullCoefficientAtRadius N (contourRadius lam z) lam z

def HighBranch (lam : ℝ) (f : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ f (omegaH lam) ∧
    (∀ z ∈ omegaH lam, f z ^ 4 = 1-spectralProduct lam z ^ 2) ∧ f 0 = 1

def LowBranch (lam : ℝ) (f : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ f (omegaL lam) ∧
    (∀ z ∈ omegaL lam, f z ^ 4 = 1-(spectralProduct lam z)⁻¹ ^ 2) ∧
    ∀ x : ℝ, 0 < x → 1 < Real.sinh x*Real.sinh (lam*x) →
      (f (x:ℂ)).im = 0 ∧ 0 < (f (x:ℂ)).re

def highPrefactor (lam : ℝ) : ℂ → ℂ :=
  if h : ∃ f, HighBranch lam f then Classical.choose h else fun _ => 0

def lowPrefactor (lam : ℝ) : ℂ → ℂ :=
  if h : ∃ f, LowBranch lam f then Classical.choose h else fun _ => 0

theorem highPrefactor_spec {lam : ℝ} (h : ∃ f, HighBranch lam f) :
    HighBranch lam (highPrefactor lam) := by
  simp only [highPrefactor, dite_eq_left h]
  exact Classical.choose_spec h

theorem lowPrefactor_spec {lam : ℝ} (h : ∃ f, LowBranch lam f) :
    LowBranch lam (lowPrefactor lam) := by
  simp only [lowPrefactor, dite_eq_left h]
  exact Classical.choose_spec h

/-- Every positive odd particle number occurs once; the power is integer. -/
def highNormalizedBulk (lam : ℝ) (z : ℂ) : ℂ :=
  highPrefactor lam z * ∑' n : ℕ, spectralProduct lam z ^ n *
    unscaledFullCoefficient (2*n+1) lam z

/-- Every positive even particle number occurs once. Zero-particle LT
magnetization is not part of this connected sum. -/
def lowNormalizedBulk (lam : ℝ) (z : ℂ) : ℂ :=
  lowPrefactor lam z * ∑' n : ℕ, spectralProduct lam z ^ (n+1) *
    unscaledFullCoefficient (2*n+2) lam z

/-- Exact onsite/offsite density split, with no omitted axes. -/
theorem fullDensity_eq_onsite_add_twice {N : ℕ} (lam : ℝ) (z : ℂ)
    (x y : Fin N → ℂ) (hx : coordinateProduct x ≠ 0) (hy : coordinateProduct y ≠ 0)
    (hx1 : 1-coordinateProduct x ≠ 0) (hy1 : 1-coordinateProduct y ≠ 0) :
    fullDensity lam z x y = onsiteDensity lam z x y + 2*offsiteDensity lam z x y := by
  unfold fullDensity onsiteDensity offsiteDensity
  rw [full_site_multiplier _ _ hx hy hx1 hy1]
  simp only [one_div]
  ring
end
end IsingBulk.Anisotropic.FormFactors
