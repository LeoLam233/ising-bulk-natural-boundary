import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Tactic

/-! Exact beta-prime periods with both integer parameters growing.
No fixed-parameter asymptotic replacement of the Gamma quotient is made. -/
namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open MeasureTheory Set
open scoped Topology

def positiveMobius (x : ℝ) : ℝ := x / (1-x)

theorem positiveMobius_hasDerivAt {x : ℝ} (hx : x ≠ 1) :
    HasDerivAt positiveMobius (1/(1-x)^2) x := by
  have hd := (hasDerivAt_id x).div ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x))
    (sub_ne_zero.mpr hx.symm)
  convert! hd using 1
  simp only [Pi.sub_apply, id_eq]
  ring

theorem positiveMobius_injOn : InjOn positiveMobius (Ioo 0 1) := by
  intro x hx y hy he
  dsimp [positiveMobius] at he
  have hx' : 1-x ≠ 0 := ne_of_gt (sub_pos.mpr hx.2)
  have hy' : 1-y ≠ 0 := ne_of_gt (sub_pos.mpr hy.2)
  have h := (div_eq_div_iff hx' hy').mp he
  nlinarith

theorem positiveMobius_image : positiveMobius '' Ioo 0 1 = Ioi 0 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact div_pos hx.1 (sub_pos.mpr hx.2)
  · intro hy
    change 0 < y at hy
    have hny : 1+y ≠ 0 := ne_of_gt (by linarith)
    refine ⟨y/(1+y), ⟨div_pos hy (by linarith), (div_lt_one (by linarith)).mpr (by linarith)⟩, ?_⟩
    dsimp [positiveMobius]
    field_simp
    ring

/-- The full Jacobian is included in this substitution. -/
theorem integral_positiveMobius (f : ℝ → ℝ) :
    (∫ x in Ioi (0 : ℝ), f x) =
      ∫ y in Ioo (0 : ℝ) 1, (1/(1-y)^2) * f (positiveMobius y) := by
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun x hx => (positiveMobius_hasDerivAt (ne_of_lt hx.2)).hasDerivWithinAt)
    positiveMobius_injOn f
  rw [positiveMobius_image] at h
  simpa only [smul_eq_mul, abs_div, abs_one, abs_pow, sq_abs] using h

theorem betaPrime_transform (m k : ℕ) {y : ℝ} (hy : y < 1) :
    (1/(1-y)^2) * (positiveMobius y)^m / (1+positiveMobius y)^(m+k+2) =
      y^m * (1-y)^k := by
  have h : 1-y ≠ 0 := ne_of_gt (sub_pos.mpr hy)
  have he : 1 + positiveMobius y = (1-y)⁻¹ := by
    dsimp [positiveMobius]
    field_simp
    ring
  rw [he]
  simp only [positiveMobius, div_pow, inv_pow, div_inv_eq_mul]
  rw [pow_add, pow_add]
  field_simp

/-- Exact reduction of the actual improper radial integral to a compact beta
integral. All exponents are integers, including the two endpoints. -/
theorem betaPrime_eq_compact (m k : ℕ) :
    (∫ x in Ioi (0 : ℝ), x^m/(1+x)^(m+k+2)) =
      ∫ y in (0 : ℝ)..1, y^m * (1-y)^k := by
  rw [integral_positiveMobius]
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro y hy
  simpa only [mul_div_assoc] using betaPrime_transform m k hy.2


theorem compactBeta_factorial (m k : ℕ) :
    (∫ y in (0 : ℝ)..1, y^m * (1-y)^k) =
      (m.factorial : ℝ) * k.factorial / (m+k+1).factorial := by
  have h := Complex.betaIntegral_eq_Gamma_mul_div ((m : ℂ)+1) ((k : ℂ)+1)
    (by simp; positivity) (by simp; positivity)
  have he : (m : ℂ)+1+((k : ℂ)+1) = ((m+k+1 : ℕ) : ℂ)+1 := by push_cast; ring
  rw [he, Complex.Gamma_nat_eq_factorial, Complex.Gamma_nat_eq_factorial,
    Complex.Gamma_nat_eq_factorial] at h
  simp only [Complex.betaIntegral, add_sub_cancel_right, Complex.cpow_natCast] at h
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  simpa only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast,
    Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_one] using h

/-- Exact beta-prime integral throughout its convergence range. Both m and k
may grow, so the Gamma ratio has not been replaced by a fixed-order asymptotic. -/
theorem betaPrime_factorial (m k : ℕ) :
    (∫ x in Ioi (0 : ℝ), x^m/(1+x)^(m+k+2)) =
      (m.factorial : ℝ) * k.factorial / (m+k+1).factorial := by
  rw [betaPrime_eq_compact, compactBeta_factorial]


/-- Exact Gamma form matching the α,j convention of (4.46). -/
theorem betaPrime_gamma (a j : ℕ) (ha : 0 < a) (haj : a ≤ j) :
    (∫ x in Ioi (0 : ℝ), x^(a-1)/(1+x)^(j+1)) =
      Real.Gamma a * Real.Gamma ((j : ℝ)+1-a) / Real.Gamma ((j : ℝ)+1) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ha)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le haj
  subst a
  subst j
  have h1 : ((m+1+k : ℕ) : ℝ)+1-(m+1 : ℕ) = (k : ℝ)+1 := by push_cast; ring
  have h2 : ((m+1+k : ℕ) : ℝ)+1 = ((m+k+1 : ℕ) : ℝ)+1 := by push_cast; ring
  rw [h1, h2, Nat.cast_succ, Real.Gamma_nat_eq_factorial,
    Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial]
  have hex : m.succ+k+1 = m+k+2 := by omega
  simpa only [Nat.succ_sub_one, hex] using betaPrime_factorial m k


theorem betaPrime_integrable (m k : ℕ) :
    IntegrableOn (fun x : ℝ => x^m/(1+x)^(m+k+2)) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [betaPrime_factorial]
  exact ne_of_gt (by positivity)

theorem betaPrime_first_moment_ratio (m k : ℕ) :
    (∫ x in Ioi (0 : ℝ), x * (x^m/(1+x)^(m+k+3))) /
      (∫ x in Ioi (0 : ℝ), x^m/(1+x)^(m+k+3)) = (m+1 : ℝ)/(k+1) := by
  have h1 : (∫ x in Ioi (0 : ℝ), x * (x^m/(1+x)^(m+k+3))) =
      (∫ x in Ioi (0 : ℝ), x^(m+1)/(1+x)^((m+1)+k+2)) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    dsimp only
    have he : m+k+3 = (m+1)+k+2 := by omega
    rw [he, pow_succ]
    ring
  have h2 : m+k+3 = m+(k+1)+2 := by omega
  rw [h1, betaPrime_factorial, h2, betaPrime_factorial]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hm : (m.factorial : ℝ) ≠ 0 := by positivity
  have hk : (k.factorial : ℝ) ≠ 0 := by positivity
  have hmk : ((m+k+1).factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

end
end IsingBulk.Anisotropic.NegativeNormalForm
