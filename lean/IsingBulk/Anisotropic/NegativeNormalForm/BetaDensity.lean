import IsingBulk.Anisotropic.NegativeNormalForm.BetaPeriod

/-! Actual beta-prime density moments. These are positive-measure estimates,
not hypotheses about a normal-form density. -/
namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open MeasureTheory Set

theorem sqrt_le_tangent {x a : ℝ} (hx : 0 ≤ x) (ha : 0 < a) :
    Real.sqrt x ≤ (x+a)/(2*Real.sqrt a) := by
  apply (le_div_iff₀ (by positivity : 0 < 2*Real.sqrt a)).2
  have hx2 := Real.sq_sqrt hx
  have ha2 := Real.sq_sqrt ha.le
  nlinarith [sq_nonneg (Real.sqrt x - Real.sqrt a)]

/-- Cauchy–Schwarz in the exact normalized beta-prime measure, proved via
an integrable tangent majorant so that integrability is not assumed. -/
theorem betaPrime_sqrt_moment_ratio (m k : ℕ) :
    (∫ x in Ioi (0 : ℝ), Real.sqrt x * (x^m/(1+x)^(m+k+3))) /
      (∫ x in Ioi (0 : ℝ), x^m/(1+x)^(m+k+3)) ≤
      Real.sqrt ((m+1 : ℝ)/(k+1)) := by
  let f : ℝ → ℝ := fun x => x^m/(1+x)^(m+k+3)
  let a : ℝ := (m+1 : ℝ)/(k+1)
  have ha : 0 < a := by dsimp [a]; positivity
  have he : m+k+3=m+(k+1)+2 := by omega
  have hf : IntegrableOn f (Ioi 0) := by simpa only [f, he] using betaPrime_integrable m (k+1)
  have hxf : IntegrableOn (fun x => x*f x) (Ioi 0) := by
    have h := betaPrime_integrable (m+1) k
    convert h using 1
    ext x
    dsimp [f]
    have he' : (m+1)+k+2=m+k+3 := by omega
    rw [he', pow_succ]
    ring
  have hm : 0 < ∫ x in Ioi (0 : ℝ), f x := by
    dsimp [f]
    rw [he, betaPrime_factorial]
    positivity
  have hmom : (∫ x in Ioi (0 : ℝ), x*f x) = a * ∫ x in Ioi (0 : ℝ), f x := by
    exact (div_eq_iff (ne_of_gt hm)).mp (betaPrime_first_moment_ratio m k)
  have hmajor : IntegrableOn (fun x => (x*f x+a*f x)/(2*Real.sqrt a)) (Ioi 0) :=
    (hxf.add (hf.const_mul a)).div_const _
  have hle : ∀ x ∈ Ioi (0 : ℝ), Real.sqrt x*f x ≤ (x*f x+a*f x)/(2*Real.sqrt a) := by
    intro x hx
    have hx0 : 0 < x := hx
    have hfx : 0 ≤ f x := by dsimp [f]; positivity
    have h := mul_le_mul_of_nonneg_right (sqrt_le_tangent (le_of_lt hx) ha) hfx
    convert h using 1
    ring
  have hsf : IntegrableOn (fun x => Real.sqrt x*f x) (Ioi 0) := by
    apply hmajor.mono'
    · exact (by fun_prop : Measurable (fun x => Real.sqrt x*f x)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 < x := hx
      rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [f]; positivity)]
      exact hle x hx
  have hint := integral_mono_ae hsf hmajor (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact hle x hx)
  rw [integral_div, integral_add hxf (hf.const_mul a), integral_const_mul, hmom] at hint
  apply (div_le_iff₀ hm).2
  convert hint using 1
  have hs : Real.sqrt a ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ha)
  field_simp
  nlinarith [Real.sq_sqrt ha.le]


/-- The moment bound in the manuscript's growing α,j variables. -/
theorem betaPrime_sqrt_order (a j : ℕ) (ha : 0 < a) (haj : a < j) :
    (∫ x in Ioi (0 : ℝ), Real.sqrt x * (x^(a-1)/(1+x)^(j+1))) /
      (∫ x in Ioi (0 : ℝ), x^(a-1)/(1+x)^(j+1)) ≤
      Real.sqrt ((a : ℝ)/((j : ℝ)-a)) := by
  have he : a-1+(j-a-1)+3=j+1 := by omega
  have h1 : ((a-1 : ℕ) : ℝ)+1=(a : ℝ) := by exact_mod_cast (show a-1+1=a by omega)
  have h2 : ((j-a-1 : ℕ) : ℝ)+1=(j : ℝ)-a := by
    have h : ((j-a-1 : ℕ) : ℝ)+1+(a : ℝ)=(j : ℝ) := by
      exact_mod_cast (show j-a-1+1+a=j by omega)
    linarith
  simpa only [he, h1, h2] using betaPrime_sqrt_moment_ratio (a-1) (j-a-1)

/-- The actual radial first moment after x=r²/(2nτ), retaining its exact
normalizing integral. -/
theorem betaPrime_scaled_sqrt_order (a j : ℕ) (ha : 0 < a) (haj : a < j)
    (c : ℝ) (hc : 0 ≤ c) :
    (∫ x in Ioi (0 : ℝ), Real.sqrt (c*x) * (x^(a-1)/(1+x)^(j+1))) /
      (∫ x in Ioi (0 : ℝ), x^(a-1)/(1+x)^(j+1)) ≤
      Real.sqrt c * Real.sqrt ((a : ℝ)/((j : ℝ)-a)) := by
  have he : (∫ x in Ioi (0 : ℝ), Real.sqrt (c*x) * (x^(a-1)/(1+x)^(j+1))) =
      Real.sqrt c * ∫ x in Ioi (0 : ℝ), Real.sqrt x * (x^(a-1)/(1+x)^(j+1)) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    dsimp only
    rw [Real.sqrt_mul hc]
    ring
  rw [he, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left (betaPrime_sqrt_order a j ha haj) (Real.sqrt_nonneg c)

end
end IsingBulk.Anisotropic.NegativeNormalForm
