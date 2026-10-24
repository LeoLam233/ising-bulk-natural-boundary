import IsingBulk.Anisotropic.RegularEdges.PositivePrimeChart
import IsingBulk.Anisotropic.Final.HighPrefactor

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open Set Filter Metric FormFactors
open scoped Topology

theorem product_sq_ne_one_of_strictU {lam : ℝ} {z : ℂ}
    (hd : spectralDet lam z≠0) (hu : |spectralU lam z|<1) : spectralProduct lam z^2≠1 := by
  intro hp
  have haux : ∀f : ℝ,f^2=1 → spectralProduct lam z=(f:ℂ) → False := by
    intro f hf hpf
    have hc := spectral_corner_identity lam z (1:ℂ) (f:ℂ) (by norm_num) (by exact_mod_cast hf)
    simp only [one_mul,hpf,sub_self,zero_pow (by decide : 2≠0),sub_eq_zero] at hc
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hc with he | he
    · have heq : spectralS z*(spectralU lam z:ℂ)+spectralT lam z*(spectralV lam z:ℂ)=
          spectralS z*(1:ℂ)+spectralT lam z*(f:ℂ) := by rw [←spectral_reconstruction hd,he]; ring
      have h := (real_coordinates_injective _ _ hd _ _ (1:ℝ) f heq).1
      simp [h] at hu
    · have heq : spectralS z*(spectralU lam z:ℂ)+spectralT lam z*(spectralV lam z:ℂ)=
          spectralS z*(-1:ℂ)+spectralT lam z*(-f:ℂ) := by rw [←spectral_reconstruction hd,he]; ring
      have h := (real_coordinates_injective _ _ hd _ _ (-1:ℝ) (-f) (by simpa using heq)).1
      simp [h] at hu
  rcases sq_eq_one_iff.mp hp with hp | hp
  · exact haux 1 (by norm_num) (by simpa using hp)
  · exact haux (-1) (by norm_num) (by simpa using hp)

/-- Actual positive V-endpoint obstruction for the complete physical HT bulk,
including its normalized physical fourth-root prefactor. -/
theorem high_positive_prime_no_extension {lam : ℝ} (hlam : 0<lam) {z : ℂ}
    (hz : z∈frontier (omegaH lam)) (hd : 0<spectralDet lam z)
    (hv : spectralV lam z=1) (hu : |spectralU lam z|<1)
    (hder : deriv (edgeMapV lam 1) z≠0) (hprime : spectralU lam z∈primePhaseCosines) :
    ¬HasDomainExtension (omegaH lam) (highNormalizedBulk lam) z := by
  obtain ⟨zeta,hζa,hζ0,r₀,hr₀,hchart⟩ := exists_oriented_V_high_chart hlam hz hd.ne'
    (Or.inl rfl : (1:ℝ)=1 ∨ (1:ℝ)= -1) hv hu hder (by simpa using hd)
  have hdζ : 0<spectralDet lam (zeta 0) := by rw [hζ0]; exact hd
  obtain ⟨r,hr,haζ,hAa,hdata⟩ := exists_positive_chart_data hζa hdζ hr₀ hchart
  have hP0 : spectralProduct lam (zeta 0)≠0 :=
    mul_ne_zero (spectralS_ne_zero_of_det_ne_zero hdζ.ne') (spectralT_ne_zero_of_det_ne_zero hdζ.ne')
  have hPa : AnalyticAt ℂ (fun u => spectralProduct lam (zeta u)) 0 :=
    (spectralProduct_analyticAt_ff lam _).comp hζa
  have hQa : AnalyticAt ℂ (fun u => 1-(spectralProduct lam (zeta u))^2) 0 :=
    analyticAt_const.sub (hPa.pow 2)
  have hQ0 : 1-(spectralProduct lam (zeta 0))^2≠0 := by
    rw [hζ0]
    exact sub_ne_zero.mpr (product_sq_ne_one_of_strictU hd.ne' hu).symm
  have hmap : MapsTo zeta (upperBall r) (omegaH lam) :=
    fun u hu => ((hdata u hu.1).2.2.2.2 hu.2).1
  have hfc : ContinuousOn (fun u => highPrefactor lam (zeta u)) (upperBall r) := by
    intro u hu
    exact (((highPrefactor_actual_spec hlam).1 _ (hmap hu)).continuousAt.comp
      (haζ u hu.1).continuousAt).continuousWithinAt
  have hfp : ∀u∈upperBall r,(highPrefactor lam (zeta u))^4=1-(spectralProduct lam (zeta u))^2 :=
    fun u hu => (highPrefactor_actual_spec hlam).2.1 _ (hmap hu)
  have hraw : ∀δ : ℝ,0<δ → δ≤r → ¬HasDomainExtension (upperBall δ) (fun u => ∑'i,
      (spectralProduct lam (zeta u))^i*unscaledFullCoefficient (2*i+1) lam (zeta u)) 0 := by
    intro δ hδ hδr
    exact (positive_prime_raw_chart_no_extension hlam hu hprime hδ
      (haζ.mono (ball_subset_ball hδr)) (hAa.mono (ball_subset_ball hδr)) hdζ
      (fun _ h => Or.inl h) (fun u hu => hdata u (ball_subset_ball hδr hu))).1
  have hno := no_extension_product_of_upper_fourth_branch hr hQa hQ0 hfc hfp hraw
  intro hext
  apply hno
  simpa only [Function.comp_apply,highNormalizedBulk] using!
    domain_extension_comp_of_mapsTo hζa hζ0 hmap hext

end
end IsingBulk.Anisotropic.RegularEdges
