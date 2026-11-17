import IsingBulk.AnisoF002.C03.NegativeHalfIntegerBase

/-!
# Complete half-integer quadratic periods

Integration by parts on the original positive real radius gives all even
radial powers.  The primitive vanishes at both endpoints and every integral
is absolutely convergent.  Combining this with the actual constrained-plane
polar identity evaluates the full even-particle first period, including
its nonzero complex phase and the independent-coordinate Mehta factor.
-/

namespace IsingBulk.AnisoF002.NegativeHT.Angular
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

def halfRadialIntegrand (a : ℕ) (τ : ℝ) (h : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ (2 * a) / ((τ : ℂ) + h * (x : ℂ) ^ 2) ^ (a + 1)

theorem halfRadialIntegrand_norm_le (a : ℕ) {τ : ℝ} {h : ℂ}
    (hτ : 0 < τ) (hh : 0 < h.re) (x : ℝ) :
    ‖halfRadialIntegrand a τ h x‖ ≤
      (h.re⁻¹) ^ a * (τ + h.re * x ^ 2)⁻¹ := by
  let D := τ + h.re * x ^ 2
  have hD : 0 < D := by dsimp [D]; positivity
  have hdn : D ≤ ‖(τ : ℂ) + h * (x : ℂ) ^ 2‖ := by
    calc
      D = ((τ : ℂ) + h * (x : ℂ) ^ 2).re := by
        rw [← Complex.ofReal_pow]
        simp only [D, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.ofReal_im, mul_zero, sub_zero]
      _ ≤ _ := Complex.re_le_norm _
  have hxD : x ^ 2 ≤ h.re⁻¹ * D := by
    dsimp [D]
    rw [inv_mul_eq_div, le_div_iff₀ hh]
    nlinarith
  have hn : ‖(x : ℂ) ^ (2 * a)‖ = (x ^ 2) ^ a := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, pow_mul, sq_abs]
  rw [halfRadialIntegrand, norm_div, hn, norm_pow]
  calc
    _ ≤ (h.re⁻¹ * D) ^ a / D ^ (a + 1) := by gcongr
    _ = _ := by
      rw [mul_pow, pow_succ]
      field_simp
      rfl

theorem halfRadialIntegrand_integrable (a : ℕ) {τ : ℝ} {h : ℂ}
    (hτ : 0 < τ) (hh : 0 < h.re) : Integrable (halfRadialIntegrand a τ h) := by
  apply ((integrable_real_inverse_quadratic hτ hh).const_mul ((h.re⁻¹) ^ a)).mono'
  · apply Continuous.aestronglyMeasurable
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro x
    exact pow_ne_zero _ (by
      simpa only [Complex.ofReal_pow] using radial_denominator_ne_zero hτ hh (sq_nonneg x))
  · exact Filter.Eventually.of_forall (halfRadialIntegrand_norm_le a hτ hh)

theorem halfRadial_primitive_tendsto (a : ℕ) (τ : ℝ) {h : ℂ} (hh : h ≠ 0) :
    Tendsto (fun x : ℝ => (x : ℂ) ^ (2 * a + 1) /
      ((τ : ℂ) + h * (x : ℂ) ^ 2) ^ (a + 1)) atTop (𝓝 0) := by
  have hr : Tendsto (fun x : ℝ => (x : ℂ) ^ 2 /
      ((τ : ℂ) + h * (x : ℂ) ^ 2)) atTop (𝓝 h⁻¹) := by
    simpa only [Function.comp_def, Complex.ofReal_pow] using
      (tendsto_radial_ratio τ hh).comp (tendsto_pow_atTop two_ne_zero)
  have hi : Tendsto (fun x : ℝ => (x : ℂ)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.ofReal_inv, Complex.ofReal_zero] using
      Complex.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0))
  have ht : Tendsto (fun x : ℝ =>
      ((x : ℂ) ^ 2 / ((τ : ℂ) + h * (x : ℂ) ^ 2)) ^ (a + 1) * (x : ℂ)⁻¹)
      atTop (𝓝 0) := by simpa using (hr.pow (a + 1)).mul hi
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [div_pow, ← pow_mul, show 2 * (a + 1) = (2 * a + 1) + 1 by omega, pow_succ]
  field_simp

theorem integral_halfRadial_step (a : ℕ) {τ : ℝ} {h : ℂ}
    (hτ : 0 < τ) (hh : 0 < h.re) :
    (∫ x in Ioi (0 : ℝ), halfRadialIntegrand (a + 1) τ h x) =
      (((2 * a + 1 : ℕ) : ℂ) *
        ∫ x in Ioi (0 : ℝ), halfRadialIntegrand a τ h x) /
      ((2 * ((a + 1 : ℕ) : ℂ)) * h) := by
  have hh0 : h ≠ 0 := by intro he; simp [he] at hh
  have ha0 : ((a + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show a + 1 ≠ 0 by omega)
  have hd : ∀ x ∈ Ici (0 : ℝ), HasDerivAt
      (fun y : ℝ => (y : ℂ) ^ (2 * a + 1) /
        ((τ : ℂ) + h * (y : ℂ) ^ 2) ^ (a + 1))
      (((2 * a + 1 : ℕ) : ℂ) * halfRadialIntegrand a τ h x -
        (2 * ((a + 1 : ℕ) : ℂ) * h) * halfRadialIntegrand (a + 1) τ h x) x := by
    intro x _
    have he : (τ : ℂ) + h * (x : ℂ) ^ 2 ≠ 0 := by
      simpa only [Complex.ofReal_pow] using radial_denominator_ne_zero hτ hh (sq_nonneg x)
    have hb : HasDerivAt (fun z : ℂ => (τ : ℂ) + h * z ^ 2)
        (h * (2 * (x : ℂ))) (x : ℂ) := by
      convert (((hasDerivAt_id (x : ℂ)).pow 2).const_mul h).const_add (τ : ℂ) using 1 <;> simp
    convert (((hasDerivAt_id (x : ℂ)).pow (2 * a + 1)).div
      (hb.pow (a + 1)) (pow_ne_zero _ he)).comp_ofReal using 1 <;>
        simp only [Pi.pow_apply, Pi.div_apply, id_eq]
    unfold halfRadialIntegrand
    simp only [Nat.add_sub_cancel, mul_one]
    rw [show 2 * (a + 1) = (2 * a) + 2 by omega, pow_add]
    field_simp
    ring
  have hi := (((halfRadialIntegrand_integrable a hτ hh).integrableOn (s := Ioi 0)).const_mul
    (((2 * a + 1 : ℕ) : ℂ))).sub
      (((halfRadialIntegrand_integrable (a + 1) hτ hh).integrableOn (s := Ioi 0)).const_mul
        (2 * ((a + 1 : ℕ) : ℂ) * h))
  have heq := integral_Ioi_of_hasDerivAt_of_tendsto' hd hi (halfRadial_primitive_tendsto a τ hh0)
  rw [integral_sub
    ((halfRadialIntegrand_integrable a hτ hh).integrableOn.const_mul _)
    ((halfRadialIntegrand_integrable (a + 1) hτ hh).integrableOn.const_mul _),
    integral_const_mul, integral_const_mul] at heq
  simp only [Complex.ofReal_zero, zero_pow (by omega : 2 * a + 1 ≠ 0),
    zero_div, sub_zero] at heq
  apply (eq_div_iff (mul_ne_zero (mul_ne_zero (by norm_num) ha0) hh0)).mpr
  linear_combination -heq

theorem integral_halfRadial_gamma (a : ℕ) {τ : ℝ} {h : ℂ}
    (hτ : 0 < τ) (hh : 0 < h.re) :
    (∫ x in Ioi (0 : ℝ), halfRadialIntegrand a τ h x) =
      (Real.Gamma ((a : ℝ) + 1 / 2) : ℂ) /
        ((Real.sqrt Real.pi : ℂ) * (a.factorial : ℂ) * h ^ a) *
      (∫ x in Ioi (0 : ℝ), ((τ : ℂ) + h * (x : ℂ) ^ 2)⁻¹) := by
  have hh0 : h ≠ 0 := by intro he; simp [he] at hh
  have hπ : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hf : ∀ j : ℕ, (j.factorial : ℂ) ≠ 0 := by
    intro j; exact_mod_cast Nat.factorial_ne_zero j
  induction a with
  | zero =>
      simp only [Nat.cast_zero, zero_add, Real.Gamma_one_half_eq, Nat.factorial_zero,
        Nat.cast_one, pow_zero, mul_one, div_self hπ, one_mul]
      simp [halfRadialIntegrand]
  | succ a ih =>
      have hg : Real.Gamma (((a + 1 : ℕ) : ℝ) + 1 / 2) =
          ((a : ℝ) + 1 / 2) * Real.Gamma ((a : ℝ) + 1 / 2) := by
        rw [Nat.cast_add, Nat.cast_one, show (a : ℝ) + 1 + 1 / 2 = ((a : ℝ) + 1 / 2) + 1 by ring,
          Real.Gamma_add_one (by positivity)]
      rw [integral_halfRadial_step a hτ hh, ih, hg, Complex.ofReal_mul,
        Nat.factorial_succ, Nat.cast_mul, pow_succ]
      push_cast
      field_simp

theorem radialShape_of_even_radialPower {d a : ℕ} (ha : radialPower d = 2 * a) :
    radialShape d = (a : ℝ) + 1 / 2 := by
  unfold radialShape
  rw [ha]
  push_cast
  ring

/-- Exact first period for half-integer shape, on the actual constrained plane. -/
theorem integral_quadraticPeriod_half_integer {d a : ℕ} (hd : 0 < d)
    (ha : radialPower d = 2 * a) {τ : ℝ} {h : ℂ}
    (hτ : 0 < τ) (hh : 0 < h.re) :
    (∫ v, quadraticPeriodIntegrand d (a + 1) τ h v ∂independentMeasure d) =
      (constrainedGaussianIntegral d : ℂ) * (Real.pi / h) ^ (1 / 2 : ℂ) *
        (Real.sqrt τ⁻¹ : ℂ) / ((a.factorial : ℂ) * h ^ a) := by
  have hΓ : (Real.Gamma ((a : ℝ) + 1 / 2) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.Gamma_pos_of_pos (by positivity : 0 < (a : ℝ) + 1 / 2)).ne'
  have hπ : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hr := vandermonde_radial_complex_integral hd
    (fun q => (1 : ℂ) / ((τ : ℂ) + h * q) ^ (a + 1))
  have hl : (fun v : constrainedPlane d =>
      planeVandermonde v • ((1 : ℂ) / ((τ : ℂ) + h * (‖v‖ ^ 2 : ℝ)) ^ (a + 1))) =
      quadraticPeriodIntegrand d (a + 1) τ h := by
    funext v
    simp only [quadraticPeriodIntegrand, Complex.real_smul, mul_one_div]
  have hq : (fun r : ℝ => r ^ radialPower d •
      ((1 : ℂ) / ((τ : ℂ) + h * (r ^ 2 : ℝ)) ^ (a + 1))) =
      halfRadialIntegrand a τ h := by
    funext r
    simp only [halfRadialIntegrand, ha, Complex.real_smul, Complex.ofReal_pow, mul_one_div]
  rw [hl, hq, integral_halfRadial_gamma a hτ hh,
    integral_inverse_complex_quadratic hτ hh, radialShape_of_even_radialPower ha,
    Complex.real_smul, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat,
    Complex.ofReal_mul] at hr
  rw [hr]
  generalize (Real.Gamma ((a : ℝ) + 1 / 2) : ℂ) = z at hΓ ⊢
  generalize (Real.sqrt Real.pi : ℂ) = p at hπ ⊢
  field_simp

theorem quadraticPeriod_half_integer_ne_zero {d a : ℕ} (hd : 0 < d)
    (ha : radialPower d = 2 * a) {τ : ℝ} {h : ℂ}
    (hτ : 0 < τ) (hh : 0 < h.re) :
    (∫ v, quadraticPeriodIntegrand d (a + 1) τ h v ∂independentMeasure d) ≠ 0 := by
  rw [integral_quadraticPeriod_half_integer hd ha hτ hh]
  have hh0 : h ≠ 0 := by intro he; simp [he] at hh
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  apply div_ne_zero
  · apply mul_ne_zero
    · exact mul_ne_zero (by exact_mod_cast (constrainedGaussianIntegral_pos d).ne')
        (Complex.cpow_ne_zero_iff.mpr (Or.inl (div_ne_zero hp hh0)))
    · exact_mod_cast (Real.sqrt_pos.mpr (inv_pos.mpr hτ)).ne'
  · exact mul_ne_zero (by exact_mod_cast Nat.factorial_ne_zero a) (pow_ne_zero _ hh0)

end
end IsingBulk.AnisoF002.NegativeHT.Angular
