import IsingBulk.Anisotropic.NegativeCycles.ModelTail
import IsingBulk.Anisotropic.NegativeNormalForm.ComplexShapePeriod

noncomputable section
namespace IsingBulk.Anisotropic.NegativeCycles
open IsingBulk.Anisotropic.NegativeDominance IsingBulk.Anisotropic.NegativeNormalForm IsingBulk.First

/-- Exact normalization of the real-part beta majorant by the literal complex period. -/
theorem betaValue_eq_complex_period_norm {n : ℕ} (ho : Odd (n+1)) (hn : 2≤n)
    (j : ℕ) (hj : alpha (n+1)≤j) (τ : ℝ) (hτ : 0<τ) (c : ℂ) (hc : 0<c.re) :
    constrainedBetaValue (n+1) j τ c.re=
      (‖c‖/c.re)^(alpha (n+1))*‖shapePeriod n j τ c‖ := by
  have ha : 0<alpha (n+1) := by
    rw [alpha_eq_derivativeOrder]
    exact IsingBulk.HT.First.derivativeOrder_pos ho (by omega)
  have hdeg : n-1+(n+1)*n=2*alpha (n+1)-1 := by
    rw [alpha_eq_derivativeOrder]
    simpa only [Nat.add_sub_cancel] using IsingBulk.HT.First.odd_shape_radial_exponent ho (by omega)
  have hcR : (c.re:ℂ)≠0 := by exact_mod_cast hc.ne'
  have hc0 : c≠0 := by intro he; simp [he] at hc
  have hnorm : 0<‖c‖/c.re := div_pos (norm_pos_iff.mpr hc0) hc
  have hre : 0<(c/(c.re:ℂ)).re := by
    rw [Complex.div_ofReal_re,div_self hc.ne']
    norm_num
  have hscale := shapePeriod_complex_rescale (by omega : 1≤n) ha hdeg j hj τ c.re hτ hc (c/(c.re:ℂ)) hre
  rw [div_mul_cancel₀ _ hcR] at hscale
  have hreal : shapePeriod n j τ (c.re:ℂ)=(constrainedBetaValue (n+1) j τ c.re:ℂ) := by
    rw [←constrainedBetaKernel_period,constrainedBetaKernel_integral ho hn j hj τ c.re hτ hc]
  have hratio : ‖c/(c.re:ℂ)‖=‖c‖/c.re := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hc]
  have hv := constrainedBetaValue_pos (show 0<n+1 by omega) j hτ hc
  rw [hscale,norm_mul,norm_zpow,hratio,zpow_neg,zpow_natCast,hreal,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hv]
  field_simp

end IsingBulk.Anisotropic.NegativeCycles
