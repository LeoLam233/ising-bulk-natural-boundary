import IsingBulk.Anisotropic.NegativeDominance.NegativeChartData
import IsingBulk.Anisotropic.Final.AnalyticInverse

namespace IsingBulk.Anisotropic.NegativeDominance
noncomputable section
open Set Filter
open scoped Topology

/-- The manuscript coordinate t and the linear edge coordinate u satisfy
u=-B(u)t, with B=-T/S. The inverse and its upper-side orientation are proved. -/
theorem exists_negative_paper_reparametrization {B : ℂ → ℂ}
    (hBa : AnalyticAt ℂ B 0) (hBi : 0<(B 0).im) :
    ∃ f : ℂ → ℂ, AnalyticAt ℂ f 0 ∧ f 0=0 ∧ deriv f 0≠0 ∧
      ∀ᶠ t in 𝓝 (0 : ℂ), 0<(B (f t)).im ∧ f t= -B (f t)*t := by
  have hB0 : B 0≠0 := by intro h; simp only [h,Complex.zero_im] at hBi; linarith
  let phi : ℂ → ℂ := fun u => -u/B u
  have hpa : AnalyticAt ℂ phi 0 := analyticAt_id.neg.div hBa hB0
  have hp0 : phi 0=0 := by simp [phi]
  have hpd : deriv phi 0= -1/B 0 := by
    have hd := (hasDerivAt_id (0 : ℂ)).neg.div hBa.differentiableAt.hasDerivAt hB0
    change HasDerivAt phi ((-1*B 0-(-0)*deriv B 0)/B 0^2) 0 at hd
    rw [hd.deriv]
    field_simp
    ring
  have hpd0 : deriv phi 0≠0 := by rw [hpd]; exact div_ne_zero (by norm_num) hB0
  obtain ⟨f,hfa,hf0,hright,_⟩ := exists_analytic_local_inverse hpa hpd0
  rw [hp0] at hfa hf0 hright
  have hBfa : AnalyticAt ℂ (fun t => B (f t)) 0 := hBa.comp_of_eq hfa hf0
  have hBf0 : 0<(B (f 0)).im := by simpa only [hf0] using hBi
  have he : ∀ᶠ t in 𝓝 (0 : ℂ), f t= -B (f t)*t := by
    filter_upwards [hright,hBfa.continuousAt.eventually_ne (by simpa only [hf0] using hB0)] with t ht hBt
    change -f t/B (f t)=t at ht
    have hm := (div_eq_iff hBt).mp ht
    linear_combination -hm
  have hfd : deriv f 0= -B 0 := by
    have heq : f =ᶠ[𝓝 (0 : ℂ)] (fun t => -B (f t)*t) := he
    rw [heq.deriv_eq]
    have hd := hBfa.differentiableAt.hasDerivAt.neg.mul (hasDerivAt_id (0 : ℂ))
    change HasDerivAt (fun t => -B (f t)*t)
      ((-deriv (fun t => B (f t)) 0)*0+(-B (f 0))*1) 0 at hd
    rw [hd.deriv]
    simp only [hf0,mul_zero,mul_one,zero_add]
  refine ⟨f,hfa,hf0,?_,?_⟩
  · rw [hfd]
    exact neg_ne_zero.mpr hB0
  filter_upwards [he,
    (Complex.continuous_im.continuousAt.comp hBfa.continuousAt).eventually_const_lt hBf0] with t ht hi
  exact ⟨hi,ht⟩

end
end IsingBulk.Anisotropic.NegativeDominance
