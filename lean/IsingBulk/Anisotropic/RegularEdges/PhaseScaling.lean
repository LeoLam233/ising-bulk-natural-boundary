import IsingBulk.Anisotropic.RegularEdges.PhaseJets

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open IsingBulk.First IsingBulk.Tail Set Filter
open scoped Topology

/-- Taylor's theorem transfers a proved quadratic input limit through an actual analytic germ. -/
theorem analytic_scaled_increment_limit {f : ℂ→ℂ} (hf : AnalyticAt ℂ f 0)
    {H : ℝ→ℂ} {a : ℂ} (hH : Tendsto H (𝓝[>] 0) (𝓝 0))
    (hQ : Tendsto (fun t : ℝ => H t/(t:ℂ)^2) (𝓝[>] 0) (𝓝 a)) :
    Tendsto (fun t : ℝ => (f (H t)-f 0)/(t:ℂ)^2) (𝓝[>] 0) (𝓝 (deriv f 0*a)) := by
  obtain ⟨g,hg,he⟩ := hf.exists_eventuallyEq_sum_add_pow_mul 2
  have hpoly (z : ℂ) :
      (∑ i∈Finset.range 2, (z^i/(i.factorial:ℂ)) • iteratedDeriv i f 0)=f 0+z*deriv f 0 := by
    simp [Finset.sum_range_succ,iteratedDeriv_zero,iteratedDeriv_one]
  have ht : Tendsto (fun t => (deriv f 0+H t*g (H t))*(H t/(t:ℂ)^2))
      (𝓝[>] 0) (𝓝 (deriv f 0*a)) := by
    simpa only [Function.comp_apply,zero_mul,add_zero] using! ((hH.mul (hg.continuousAt.tendsto.comp hH)).const_add (deriv f 0)).mul hQ
  apply ht.congr'
  filter_upwards [hH.eventually he,self_mem_nhdsWithin] with t ht ht0
  rw [ht,hpoly]
  have htne : (t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (show (0:ℝ)<t from ht0).ne'
  simp only [smul_eq_mul]
  field_simp
  ring

def scaledEdgeIncrement (B : ℂ→ℂ) (q : ℝ) (t : ℝ) : ℂ :=
  Complex.I*(t:ℂ)^2+B (Complex.I*(t:ℂ)^2)*(1-Complex.cos ((t:ℂ)*(q:ℂ)))

theorem scaledEdgeIncrement_tendsto {B : ℂ→ℂ} (hB : ContinuousAt B 0) (q : ℝ) :
    Tendsto (scaledEdgeIncrement B q) (𝓝[>] 0) (𝓝 0) := by
  have hu : Tendsto (fun t : ℝ => Complex.I*(t:ℂ)^2) (𝓝[>] 0) (𝓝 0) := by
    simpa using! ((Complex.continuous_ofReal.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds).pow 2 |>.const_mul Complex.I
  have hcos : Tendsto (fun t : ℝ => Complex.cos ((t:ℂ)*(q:ℂ))) (𝓝[>] 0) (𝓝 1) := by
    have hh : Continuous (fun t : ℝ => Complex.cos ((t:ℂ)*(q:ℂ))) := by fun_prop
    simpa using! (hh.tendsto 0).mono_left nhdsWithin_le_nhds
  simpa only [scaledEdgeIncrement,Function.comp_apply,sub_self,mul_zero,add_zero,zero_add] using!
    hu.add ((hB.tendsto.comp hu).mul (hcos.const_sub (1:ℂ)))

theorem scaledEdgeIncrement_quotient_limit {B : ℂ→ℂ} (hB : ContinuousAt B 0) (q : ℝ) :
    Tendsto (fun t : ℝ => scaledEdgeIncrement B q t/(t:ℂ)^2) (𝓝[>] 0)
      (𝓝 (Complex.I+B 0*(q:ℂ)^2/2)) := by
  have hu : Tendsto (fun t : ℝ => Complex.I*(t:ℂ)^2) (𝓝[>] 0) (𝓝 0) := by
    simpa using! ((Complex.continuous_ofReal.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds).pow 2 |>.const_mul Complex.I
  have ht := ((hB.tendsto.comp hu).mul (angular_cosine_quadratic_limit q)).const_add Complex.I
  have ht' : Tendsto (fun t : ℝ => Complex.I+B (Complex.I*(t:ℂ)^2)*
      ((1-Complex.cos ((t:ℂ)*(q:ℂ)))/(t:ℂ)^2)) (𝓝[>] 0)
      (𝓝 (Complex.I+B 0*(q:ℂ)^2/2)) := by simpa only [Function.comp_apply,mul_div_assoc] using! ht
  apply ht'.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htne : (t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (show (0:ℝ)<t from ht).ne'
  unfold scaledEdgeIncrement
  field_simp

theorem edgeParamRoot_scaled_increment_limit {b : ℝ} (hb : |b|<1) {B : ℂ→ℂ}
    (hB : ContinuousAt B 0) (q : ℝ) :
    Tendsto (fun t : ℝ => (edgeParamRoot b B (Complex.I*(t:ℂ)^2) (t*q)-continuedRoot (b:ℂ))/(t:ℂ)^2)
      (𝓝[>] 0) (𝓝 ((Complex.I*continuedRoot (b:ℂ)/(Real.sqrt (1-b^2):ℂ))*
        (Complex.I+B 0*(q:ℂ)^2/2))) := by
  have ha : AnalyticAt ℂ (fun w => continuedRoot ((b:ℂ)+w)) 0 := by
    have hh : AnalyticAt ℂ continuedRoot ((b:ℂ)+0) := by
      simpa using continuedRoot_analyticAt (show (b:ℂ)∈continuedRootDomain from Or.inr (by simpa using hb))
    simpa using! hh.comp (f := fun w : ℂ => (b:ℂ)+w) (analyticAt_const.add analyticAt_id)
  have hd : deriv (fun w => continuedRoot ((b:ℂ)+w)) 0=
      Complex.I*continuedRoot (b:ℂ)/(Real.sqrt (1-b^2):ℂ) := by
    have hh := (edgeParamRoot_parameter_hasDerivAt hb B).deriv
    simpa only [edgeParamRoot,edgeParamW,Real.cos_zero,Complex.ofReal_one,sub_self,mul_zero,add_zero] using hh
  have ht := analytic_scaled_increment_limit ha (scaledEdgeIncrement_tendsto hB q)
    (scaledEdgeIncrement_quotient_limit hB q)
  rw [hd] at ht
  convert ht using 1
  ext t
  simp only [edgeParamRoot,edgeParamW,scaledEdgeIncrement,Complex.ofReal_mul,Complex.ofReal_cos,add_zero]
  congr 2
  ring

end
end IsingBulk.Anisotropic.RegularEdges
