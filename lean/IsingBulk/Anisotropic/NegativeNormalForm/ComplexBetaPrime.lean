import IsingBulk.Anisotropic.NegativeNormalForm.ComplexCompactBeta

namespace IsingBulk.Anisotropic.NegativeNormalForm
noncomputable section
open MeasureTheory Set

theorem integral_positiveMobius_complex (f : ℝ → ℂ) :
    (∫ x in Ioi (0:ℝ), f x)=
      ∫ y in Ioo (0:ℝ) 1, (1/(1-y)^2:ℝ) • f (positiveMobius y) := by
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun x hx => (positiveMobius_hasDerivAt (ne_of_lt hx.2)).hasDerivWithinAt)
    positiveMobius_injOn f
  rw [positiveMobius_image] at h
  simpa only [abs_div,abs_one,abs_pow,sq_abs] using h

theorem complexBetaPrime_transform (m k : ℕ) (h : ℂ) (hh : 0<h.re)
    {y : ℝ} (hy : y∈Ioo (0:ℝ) 1) :
    (1/(1-y)^2:ℝ) • ((positiveMobius y:ℂ)^m/(1+h*(positiveMobius y:ℂ))^(m+k+2))=
      complexCompactBetaIntegrand m k h y := by
  have hyc : 1-(y:ℂ)≠0 := by exact_mod_cast (sub_ne_zero.mpr (ne_of_gt hy.2))
  have hden := complexBetaMobius_den_ne h hh ⟨hy.1.le,hy.2.le⟩
  have he : 1+h*(positiveMobius y:ℂ)=(1+(h-1)*(y:ℂ))/(1-(y:ℂ)) := by
    simp only [positiveMobius,Complex.ofReal_div,Complex.ofReal_sub,Complex.ofReal_one]
    field_simp [hyc]
    ring
  rw [he]
  simp only [Complex.real_smul,positiveMobius,complexCompactBetaIntegrand,
    Complex.ofReal_div,Complex.ofReal_sub,Complex.ofReal_one,Complex.ofReal_pow,
    div_pow,pow_add]
  field_simp [hyc,hden]

/-- Actual complex beta-prime integral, uniformly in both integer parameters. -/
theorem complexBetaPrime_factorial (m k : ℕ) (h : ℂ) (hh : 0<h.re) :
    (∫ x in Ioi (0:ℝ), (x:ℂ)^m/(1+h*(x:ℂ))^(m+k+2))=
      ((m.factorial:ℂ)*k.factorial/(m+k+1).factorial)/h^(m+1) := by
  rw [integral_positiveMobius_complex]
  rw [←complexCompactBeta_factorial m k h hh]
  rw [intervalIntegral.integral_of_le zero_le_one,integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro y hy
  exact complexBetaPrime_transform m k h hh hy

end
end IsingBulk.Anisotropic.NegativeNormalForm
