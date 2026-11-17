import IsingBulk.AnisoF002.NegativeHT.GammaCorrection
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination

/-!
# The complex beta period on the original real half-line

F002, equation `eq:rc-complex-beta`, separates the constrained Vandermonde
integral into an angular constant and an integral over a positive real
radius.  This file evaluates that actual radial integral for every integer
exponent in its convergence range and every complex curvature of positive
real part.  The integration variable stays real throughout.
-/

namespace IsingBulk.AnisoF002.NegativeHT

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

/-- The exact radial integrand after Vandermonde homogeneity.  The integer
`a` is alpha minus one, and `m` is the Taylor order minus alpha. -/
def complexRadialIntegrand (a m : ℕ) (τ : ℝ) (h : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ)^a / ((τ : ℂ) + h * x)^(a+m+2)

theorem radial_denominator_re_pos {τ : ℝ} {h : ℂ}
    (hτ : 0 < τ) (hh : 0 < h.re) {x : ℝ} (hx : 0 ≤ x) :
    0 < ((τ : ℂ) + h * x).re := by
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  exact add_pos_of_pos_of_nonneg hτ (mul_nonneg hh.le hx)

theorem radial_denominator_ne_zero {τ : ℝ} {h : ℂ}
    (hτ : 0 < τ) (hh : 0 < h.re) {x : ℝ} (hx : 0 ≤ x) :
    (τ : ℂ) + h * x ≠ 0 := by
  intro he
  have hp := radial_denominator_re_pos hτ hh hx
  rw [he] at hp
  simp at hp

/-- A positive real majorant, with the full complex curvature retained in
the actual integrand. -/
theorem complexRadialIntegrand_norm_le (a m : ℕ) {τ : ℝ} {h : ℂ}
    (hτ : 0 < τ) (hh : 0 < h.re) {x : ℝ} (hx : 0 ≤ x) :
    ‖complexRadialIntegrand a m τ h x‖ ≤
      (h.re^(a+m+2))⁻¹ * (x + τ/h.re)^(-((m+2 : ℕ) : ℝ)) := by
  have hshift : 0 < τ / h.re := div_pos hτ hh
  have hy : 0 < x + τ / h.re := add_pos_of_nonneg_of_pos hx hshift
  have hd : h.re * (x + τ/h.re) ≤ ‖(τ : ℂ) + h*x‖ := by
    have hr := Complex.re_le_norm ((τ : ℂ) + h*x)
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, mul_zero, sub_zero] at hr
    have he : h.re * (x + τ/h.re) = τ + h.re*x := by field_simp; ring
    rwa [he]
  unfold complexRadialIntegrand
  rw [norm_div, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hx]
  calc
    x^a / ‖(τ : ℂ) + h*x‖^(a+m+2) ≤
        (x + τ/h.re)^a / (h.re*(x + τ/h.re))^(a+m+2) := by
      gcongr
      linarith
    _ = (h.re^(a+m+2))⁻¹ * (x + τ/h.re)^(-((m+2 : ℕ) : ℝ)) := by
      rw [Real.rpow_neg hy.le, Real.rpow_natCast, mul_pow,
        show a+m+2 = a+(m+2) by omega, pow_add]
      field_simp
      simp only [pow_add]

theorem continuousOn_complexRadialIntegrand (a m : ℕ) {τ : ℝ} {h : ℂ}
    (hτ : 0 < τ) (hh : 0 < h.re) :
    ContinuousOn (complexRadialIntegrand a m τ h) (Ici 0) := by
  apply ContinuousOn.div
  · fun_prop
  · fun_prop
  · intro x hx
    exact pow_ne_zero _ (radial_denominator_ne_zero hτ hh hx)

/-- Absolute convergence holds on the complete positive real radius, with
no finite radial cutoff and no restriction on the phase beyond Re h > 0. -/
theorem integrableOn_complexRadialIntegrand (a m : ℕ) {τ : ℝ} {h : ℂ}
    (hτ : 0 < τ) (hh : 0 < h.re) :
    IntegrableOn (complexRadialIntegrand a m τ h) (Ioi 0) := by
  have hbase : IntegrableOn (fun x : ℝ =>
      (h.re^(a+m+2))⁻¹ * (x + τ/h.re)^(-((m+2 : ℕ) : ℝ))) (Ioi 0) := by
    apply Integrable.const_mul
    apply integrableOn_add_rpow_Ioi_of_lt
    · have hm : (0 : ℝ) ≤ m := by positivity
      push_cast
      linarith
    · have hs : 0 < τ/h.re := div_pos hτ hh
      linarith
  apply Integrable.mono' hbase
  · exact ((continuousOn_complexRadialIntegrand a m hτ hh).mono
      Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact complexRadialIntegrand_norm_le a m hτ hh hx.le

theorem tendsto_radial_inverse (τ : ℝ) {h : ℂ} (hh : h ≠ 0) :
    Tendsto (fun x : ℝ => ((τ : ℂ) + h*x)⁻¹) atTop (𝓝 0) := by
  have hi : Tendsto (fun x : ℝ => (x : ℂ)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.ofReal_inv, Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0))
  have hr : Tendsto (fun x : ℝ => ((τ : ℂ)*(x : ℂ)⁻¹+h)⁻¹)
      atTop (𝓝 h⁻¹) := by
    simpa using ((hi.const_mul (τ : ℂ)).add_const h).inv₀ (by simpa using hh)
  have ht : Tendsto (fun x : ℝ => (x : ℂ)⁻¹ *
      ((τ : ℂ)*(x : ℂ)⁻¹+h)⁻¹) atTop (𝓝 0) := by
    simpa using hi.mul hr
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [← mul_inv]
  congr 1
  field_simp

theorem tendsto_radial_ratio (τ : ℝ) {h : ℂ} (hh : h ≠ 0) :
    Tendsto (fun x : ℝ => (x : ℂ)/((τ : ℂ)+h*x)) atTop (𝓝 h⁻¹) := by
  have hi : Tendsto (fun x : ℝ => (x : ℂ)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.ofReal_inv, Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0))
  have hr : Tendsto (fun x : ℝ => ((τ : ℂ)*(x : ℂ)⁻¹+h)⁻¹)
      atTop (𝓝 h⁻¹) := by
    simpa using ((hi.const_mul (τ : ℂ)).add_const h).inv₀ (by simpa using hh)
  apply hr.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [show (τ : ℂ)*(x : ℂ)⁻¹+h = ((τ : ℂ)+h*x)/(x : ℂ) by field_simp]
  exact inv_div _ _

theorem tendsto_radial_primitive (a m : ℕ) (τ : ℝ) {h : ℂ} (hh : h ≠ 0) :
    Tendsto (fun x : ℝ => (x : ℂ)^(a+1) /
      ((τ : ℂ)+h*x)^(a+m+2)) atTop (𝓝 0) := by
  have hr := (tendsto_radial_ratio τ hh).pow (a+1)
  have hi := (tendsto_radial_inverse τ hh).pow (m+1)
  have ht : Tendsto (fun x : ℝ => ((x : ℂ)/((τ : ℂ)+h*x))^(a+1) *
      (((τ : ℂ)+h*x)⁻¹)^(m+1)) atTop (𝓝 0) := by
    simpa using hr.mul hi
  convert ht using 1
  ext x
  simp only [div_eq_mul_inv, mul_pow, ← inv_pow, mul_assoc, ← pow_add]
  congr 2
  omega

/-- Evaluation of the real half-line integral with no power in the radial
numerator. This is the base case for the complete integer beta recurrence. -/
theorem integral_complexRadialIntegrand_zero (m : ℕ) {τ : ℝ} {h : ℂ}
    (hτ : 0 < τ) (hh : 0 < h.re) :
    (∫ x in Ioi (0 : ℝ), complexRadialIntegrand 0 m τ h x) =
      1 / ((m+1 : ℕ) * h * (τ : ℂ)^(m+1)) := by
  have hh0 : h ≠ 0 := by
    intro he
    simp [he] at hh
  have hm0 : ((m+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show m+1 ≠ 0 by omega)
  have hd : ∀ x ∈ Ici (0 : ℝ), HasDerivAt
      (fun y : ℝ => (((τ : ℂ)+h*y)^(m+1))⁻¹)
      (-((m+1 : ℕ) : ℂ)*h*complexRadialIntegrand 0 m τ h x) x := by
    intro x hx
    have he := radial_denominator_ne_zero hτ hh hx
    have hb : HasDerivAt (fun z : ℂ => (τ : ℂ)+h*z) h (x : ℂ) := by
      simpa using ((hasDerivAt_id (x : ℂ)).const_mul h).const_add (τ : ℂ)
    convert ((hb.pow (m+1)).inv (pow_ne_zero _ he)).comp_ofReal using 1
    simp only [Pi.pow_apply]
    unfold complexRadialIntegrand
    simp only [Nat.add_sub_cancel, Nat.zero_add, pow_zero]
    field_simp
    ring
  have hi := (integrableOn_complexRadialIntegrand 0 m hτ hh).const_mul
    (-((m+1 : ℕ) : ℂ)*h)
  have ht : Tendsto (fun y : ℝ => (((τ : ℂ)+h*y)^(m+1))⁻¹)
      atTop (𝓝 0) := by
    simpa only [inv_pow, zero_pow (by omega : m+1 ≠ 0)] using
      (tendsto_radial_inverse τ hh0).pow (m+1)
  have heq := integral_Ioi_of_hasDerivAt_of_tendsto' hd hi ht
  rw [integral_const_mul] at heq
  simp only [Complex.ofReal_zero, mul_zero, add_zero, zero_sub] at heq
  have hτ0 : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
  apply (eq_div_iff (mul_ne_zero (mul_ne_zero hm0 hh0) (pow_ne_zero _ hτ0))).mpr
  field_simp at heq ⊢
  linear_combination -heq

/-- Integration by parts on the full real half-line gives the integer
beta recurrence. Both endpoints and absolute convergence are proved. -/
theorem integral_complexRadialIntegrand_step (a m : ℕ) {τ : ℝ} {h : ℂ}
    (hτ : 0 < τ) (hh : 0 < h.re) :
    (∫ x in Ioi (0 : ℝ), complexRadialIntegrand (a+1) m τ h x) =
      (((a+1 : ℕ) : ℂ) *
        (∫ x in Ioi (0 : ℝ), complexRadialIntegrand a m τ h x)) /
          (((a+m+2 : ℕ) : ℂ) * h) := by
  have hh0 : h ≠ 0 := by intro he; simp [he] at hh
  have hk0 : ((a+m+2 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (show a+m+2 ≠ 0 by omega)
  have hd : ∀ x ∈ Ici (0 : ℝ), HasDerivAt
      (fun y : ℝ => (y : ℂ)^(a+1) / ((τ : ℂ)+h*y)^(a+m+2))
      (((a+1 : ℕ) : ℂ)*complexRadialIntegrand a m τ h x -
        ((a+m+2 : ℕ) : ℂ)*h*complexRadialIntegrand (a+1) m τ h x) x := by
    intro x hx
    have he := radial_denominator_ne_zero hτ hh hx
    have hb : HasDerivAt (fun z : ℂ => (τ : ℂ)+h*z) h (x : ℂ) := by
      simpa using ((hasDerivAt_id (x : ℂ)).const_mul h).const_add (τ : ℂ)
    convert (((hasDerivAt_id (x : ℂ)).pow (a+1)).div
      (hb.pow (a+m+2)) (pow_ne_zero _ he)).comp_ofReal using 1 <;>
        simp only [Pi.pow_apply, Pi.div_apply, id_eq]
    unfold complexRadialIntegrand
    simp only [Nat.add_sub_cancel, mul_one,
      show a+m+2-1 = a+m+1 by omega]
    field_simp
    ring
  have hi := ((integrableOn_complexRadialIntegrand a m hτ hh).const_mul
    ((a+1 : ℕ) : ℂ)).sub
      ((integrableOn_complexRadialIntegrand (a+1) m hτ hh).const_mul
        (((a+m+2 : ℕ) : ℂ)*h))
  have ht := tendsto_radial_primitive a m τ hh0
  have heq := integral_Ioi_of_hasDerivAt_of_tendsto' hd hi ht
  rw [integral_sub
    ((integrableOn_complexRadialIntegrand a m hτ hh).const_mul _)
    ((integrableOn_complexRadialIntegrand (a+1) m hτ hh).const_mul _),
    integral_const_mul, integral_const_mul] at heq
  simp only [Complex.ofReal_zero, zero_pow (by omega : a+1 ≠ 0),
    zero_div, sub_zero] at heq
  apply (eq_div_iff (mul_ne_zero hk0 hh0)).mpr
  linear_combination -heq

/-- Exact complex radial beta integral in its entire integer convergence
range. The curvature may have either imaginary sign. -/
theorem integral_complexRadialBeta (a m : ℕ) {τ : ℝ} {h : ℂ}
    (hτ : 0 < τ) (hh : 0 < h.re) :
    (∫ x in Ioi (0 : ℝ), complexRadialIntegrand a m τ h x) =
      ((Nat.factorial a : ℂ)*(Nat.factorial m : ℂ)) /
        ((Nat.factorial (a+m+1) : ℂ) * h^(a+1) * (τ : ℂ)^(m+1)) := by
  have hh0 : h ≠ 0 := by intro he; simp [he] at hh
  have hτ0 : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
  have hfact : ∀ k : ℕ, (Nat.factorial k : ℂ) ≠ 0 := by
    intro k; exact_mod_cast Nat.factorial_ne_zero k
  induction a with
  | zero =>
      rw [integral_complexRadialIntegrand_zero m hτ hh]
      simp only [Nat.factorial_zero, Nat.cast_one, one_mul, Nat.zero_add, pow_one]
      rw [Nat.factorial_succ, Nat.cast_mul]
      field_simp [hfact m]
  | succ a ih =>
      rw [integral_complexRadialIntegrand_step a m hτ hh, ih]
      rw [show a+1+m+1 = (a+m+1)+1 by omega]
      rw [Nat.factorial_succ a, Nat.factorial_succ (a+m+1)]
      push_cast
      simp only [pow_succ]
      field_simp [hfact (a+m+1)]
      ring

end

end IsingBulk.AnisoF002.NegativeHT
