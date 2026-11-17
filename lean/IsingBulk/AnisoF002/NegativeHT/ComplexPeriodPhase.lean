import IsingBulk.AnisoF002.NegativeHT.ComplexRadialBeta
import IsingBulk.AnisoF002.NegativeHT.RealCyclePhase
import IsingBulk.AnisoF002.NegativeHT.ComplexModel

/-!
# The exact radial beta period and its positive-majorant comparison

The radial slope `h` here equals F002's curvature divided by `2*n`.
All integrations remain over the original positive real radius.  This
file connects the evaluated integral to its exact phase cost; construction
of the Vandermonde angular measure and physical moving pole is separate.
-/

namespace IsingBulk.AnisoF002.NegativeHT

open MeasureTheory Set

noncomputable section

/-- The radial beta integral in the paper's exponent and Taylor-order
variables, before multiplication by the constrained angular constant. -/
def complexRadialPeriod (α j : ℕ) (τ : ℝ) (h : ℂ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), (x : ℂ)^(α-1) / ((τ : ℂ)+h*x)^(j+1)

/-- Exact factorial form of the radial integral at every convergent
integer order. -/
theorem complexRadialPeriod_eq (α j : ℕ) {τ : ℝ} {h : ℂ}
    (hα : 0<α) (hj : α≤j) (hτ : 0<τ) (hh : 0<h.re) :
    complexRadialPeriod α j τ h =
      ((Nat.factorial (α-1) : ℂ)*(Nat.factorial (j-α) : ℂ)) /
        ((Nat.factorial j : ℂ)*h^α*(τ : ℂ)^(j+1-α)) := by
  have h1 : α-1+(j-α)+2 = j+1 := by omega
  have h2 : α-1+(j-α)+1 = j := by omega
  have h3 : α-1+1 = α := by omega
  have h4 : j-α+1 = j+1-α := by omega
  simpa only [complexRadialPeriod, complexRadialIntegrand, h1, h2, h3, h4]
    using integral_complexRadialBeta (α-1) (j-α) hτ hh

/-- The evaluated real-cycle radial period retains the exact complex
curvature modulus. -/
theorem norm_complexRadialPeriod (α j : ℕ) {τ : ℝ} {h : ℂ}
    (hα : 0<α) (hj : α≤j) (hτ : 0<τ) (hh : 0<h.re) :
    ‖complexRadialPeriod α j τ h‖ =
      ((Nat.factorial (α-1) : ℝ)*(Nat.factorial (j-α) : ℝ)) /
        ((Nat.factorial j : ℝ)*‖h‖^α*τ^(j+1-α)) := by
  rw [complexRadialPeriod_eq α j hα hj hτ hh]
  simp only [norm_div, norm_mul, norm_pow, Complex.norm_natCast,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ]

/-- The positive real-part majorant divided by the modulus of the actual
complex radial integral has precisely the phase ratio in F002. -/
theorem radialPeriod_majorant_ratio (α j : ℕ) {τ : ℝ} {h : ℂ}
    (hα : 0<α) (hj : α≤j) (hτ : 0<τ) (hh : 0<h.re) :
    ‖complexRadialPeriod α j τ (h.re : ℂ)‖ /
        ‖complexRadialPeriod α j τ h‖ = (‖h‖/h.re)^α := by
  have hh0 : h ≠ 0 := by intro he; simp [he] at hh
  have hn0 : ‖h‖ ≠ 0 := norm_ne_zero_iff.mpr hh0
  have hf0 : ∀ k : ℕ, (Nat.factorial k : ℝ) ≠ 0 := by
    intro k; exact_mod_cast Nat.factorial_ne_zero k
  rw [norm_complexRadialPeriod α j hα hj hτ (by simpa using hh),
    norm_complexRadialPeriod α j hα hj hτ hh]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh, div_pow]
  field_simp

/-- Quantitative phase comparison of the actual full radial integrals. -/
theorem radialPeriod_phase_cost (α j : ℕ) {τ : ℝ} {h : ℂ}
    (hα : 0<α) (hj : α≤j) (hτ : 0<τ) (hh : 0<h.re) :
    1 ≤ ‖complexRadialPeriod α j τ (h.re : ℂ)‖ /
        ‖complexRadialPeriod α j τ h‖ ∧
      ‖complexRadialPeriod α j τ (h.re : ℂ)‖ /
        ‖complexRadialPeriod α j τ h‖ ≤
          Real.exp ((α : ℝ)*h.im^2/(2*h.re^2)) := by
  rw [radialPeriod_majorant_ratio α j hα hj hτ hh]
  exact curvature_phase_cost α hh

/-- Changing the curvature to its real part in the exact model retains
every other factorial, gamma, anisotropy and winding normalization. -/
theorem modelMagnitude_curvature_change (n j : ℕ) (B s τ : ℝ)
    {h : ℂ} (hh : 0<h.re) :
    modelMagnitude n j B h.re s τ =
      (‖h‖/h.re)^(particleExponent n) * modelMagnitude n j B ‖h‖ s τ := by
  have hh0 : h ≠ 0 := by intro he; simp [he] at hh
  have hn : 0<‖h‖ := norm_pos_iff.mpr hh0
  have hp : h.re^(-(particleExponent n : ℝ)) =
      (‖h‖/h.re)^(particleExponent n) * ‖h‖^(-(particleExponent n : ℝ)) := by
    rw [Real.rpow_neg hh.le, Real.rpow_natCast,
      Real.rpow_neg hn.le, Real.rpow_natCast, div_pow]
    field_simp
  unfold modelMagnitude modelPrefactor
  rw [hp]
  ring

/-- Exact majorant relation for the previously stored full complex model.
This uses the actual norm theorem of that model, including its B phase. -/
theorem norm_modelCoefficient_realPart_curvature (n j : ℕ) (B : ℂ) (s τ : ℝ)
    {h : ℂ} (hn : 0<n) (hs : 0<s) (hτ : 0<τ) (hh : 0<h.re) :
    ‖modelCoefficient n j B (h.re : ℂ) s τ‖ =
      (‖h‖/h.re)^(particleExponent n) * ‖modelCoefficient n j B h s τ‖ := by
  rw [norm_modelCoefficient n j B (h.re : ℂ) s τ hn hs hτ,
    norm_modelCoefficient n j B h s τ hn hs hτ,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]
  exact modelMagnitude_curvature_change n j ‖B‖ s τ hh

/-- Quantitative phase cost for the complete exact scalar model. -/
theorem modelCoefficient_phase_cost (n j : ℕ) (B : ℂ) (s τ : ℝ)
    {h : ℂ} (hn : 0<n) (hs : 0<s) (hτ : 0<τ) (hh : 0<h.re) :
    ‖modelCoefficient n j B h s τ‖ ≤
        ‖modelCoefficient n j B (h.re : ℂ) s τ‖ ∧
      ‖modelCoefficient n j B (h.re : ℂ) s τ‖ ≤
        Real.exp ((particleExponent n : ℝ)*h.im^2/(2*h.re^2)) *
          ‖modelCoefficient n j B h s τ‖ := by
  rw [norm_modelCoefficient_realPart_curvature n j B s τ hn hs hτ hh]
  have hc := curvature_phase_cost (particleExponent n) hh
  constructor
  · simpa using mul_le_mul_of_nonneg_right hc.1
      (norm_nonneg (modelCoefficient n j B h s τ))
  · exact mul_le_mul_of_nonneg_right hc.2
      (norm_nonneg (modelCoefficient n j B h s τ))

end

end IsingBulk.AnisoF002.NegativeHT
