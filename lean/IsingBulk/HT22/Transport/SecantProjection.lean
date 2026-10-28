import IsingBulk.HT22.Transport.ProjectedProduct
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Protected cone bounds survive genuine integration along the
fixed-occupancy connecting arc; this is not a mean-value theorem for complex
functions. The derivative bounds must come from the physical inverse. -/
namespace IsingBulk.HT22
noncomputable section
open MeasureTheory Set

theorem secant_projected_cone {f f' : ℝ → ℂ} {a b κ : ℝ} {phase : ℂ}
    (hab : a≤b) (hκ : 0≤κ)
    (hderiv : ∀ x∈Icc a b, HasDerivAt f (f' x) x)
    (hcont : ContinuousOn f' (Icc a b))
    (hcone : ∀ x∈Icc a b, κ*‖f' x‖≤(phase*f' x).re) :
    κ*‖f b-f a‖≤(phase*(f b-f a)).re := by
  have hi : IntervalIntegrable f' volume a b := hcont.intervalIntegrable_of_Icc hab
  have hR : ContinuousOn (fun x => (phase*f' x).re) (Icc a b) :=
    Complex.continuous_re.comp_continuousOn (continuousOn_const.mul hcont)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (by simpa only [uIcc_of_le hab] using hderiv) hi
  have hproj : (∫ x in a..b, (phase*f' x).re)=(phase*(f b-f a)).re := by
    have hh := Complex.reCLM.intervalIntegral_comp_comm (hi.const_mul phase)
    change (∫ x in a..b, (phase*f' x).re)=(∫ x in a..b, phase*f' x).re at hh
    rw [intervalIntegral.integral_const_mul,he] at hh
    exact hh
  have hmono := intervalIntegral.integral_mono_on hab (hi.norm.const_mul κ)
    (hR.intervalIntegrable_of_Icc hab) hcone
  rw [intervalIntegral.integral_const_mul,hproj] at hmono
  have hnorm := intervalIntegral.norm_integral_le_integral_norm (f:=f') (μ:=volume) hab
  rw [he] at hnorm
  exact (mul_le_mul_of_nonneg_left hnorm hκ).trans hmono

theorem secant_projected_size {f f' : ℝ → ℂ} {a b L : ℝ} {phase : ℂ}
    (hab : a≤b)
    (hderiv : ∀ x∈Icc a b, HasDerivAt f (f' x) x)
    (hcont : ContinuousOn f' (Icc a b))
    (hsize : ∀ x∈Icc a b, L≤(phase*f' x).re) :
    L*(b-a)≤(phase*(f b-f a)).re := by
  have hi : IntervalIntegrable f' volume a b := hcont.intervalIntegrable_of_Icc hab
  have hR : ContinuousOn (fun x => (phase*f' x).re) (Icc a b) :=
    Complex.continuous_re.comp_continuousOn (continuousOn_const.mul hcont)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (by simpa only [uIcc_of_le hab] using hderiv) hi
  have hproj : (∫ x in a..b, (phase*f' x).re)=(phase*(f b-f a)).re := by
    have hh := Complex.reCLM.intervalIntegral_comp_comm (hi.const_mul phase)
    change (∫ x in a..b, (phase*f' x).re)=(∫ x in a..b, phase*f' x).re at hh
    rw [intervalIntegral.integral_const_mul,he] at hh
    exact hh
  have hmono := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => L) volume a b)
    (hR.intervalIntegrable_of_Icc hab) hsize
  rw [intervalIntegral.integral_const,hproj] at hmono
  simpa only [smul_eq_mul,mul_comm] using hmono

end
end IsingBulk.HT22
