import IsingBulk.Anisotropic.RegularEdges.NegativeLowLeading
import IsingBulk.Anisotropic.RegularEdges.PositiveEndpointLow
import IsingBulk.Anisotropic.NegativeDominance.NegativeChartData

namespace IsingBulk.Anisotropic.RegularEdges
noncomputable section
open Set Filter Metric FormFactors NegativeDominance
open scoped Topology

theorem exists_negative_general_chart_data {lam b : ℝ} {D : Set ℂ} {zeta : ℂ→ℂ} {r₀ : ℝ}
    (hza : AnalyticAt ℂ zeta 0) (hd : spectralDet lam (zeta 0)<0) (hr₀ : 0<r₀)
    (hchart : ∀u : ℂ,‖u‖<r₀ → edgeMapV lam (-1) (zeta u)=(b:ℂ)+u ∧ (0<u.im → zeta u∈D)) :
    ∃r : ℝ,0<r ∧ AnalyticOnNhd ℂ zeta (ball 0 r) ∧
      AnalyticOnNhd ℂ (negativeChartRoot lam zeta) (ball 0 r) ∧
      ∀u∈ball 0 r,0<(negativeChartB lam zeta u).im ∧ spectralS (zeta u)≠0 ∧
        negativeChartRoot lam zeta u≠0 ∧ edgeMapV lam (-1) (zeta u)=(b:ℂ)+u ∧
        (0<u.im → zeta u∈D\{0}) := by
  have hS := spectralS_ne_zero_of_det_ne_zero hd.ne
  have hT := spectralT_ne_zero_of_det_ne_zero hd.ne
  have hP : spectralProduct lam (zeta 0)≠0 := mul_ne_zero hS hT
  have hAa := negativeChartRoot_analyticAt hza hP
  have hA0 : negativeChartRoot lam zeta 0≠0 := localParticleRoot_ne_zero hP
  have hB0 : 0<(negativeChartB lam zeta 0).im := by
    exact negative_ratio_im_pos hd
  have hBa := negativeChartB_analyticAt (lam := lam) hza hS
  have hSa := negativeChartS_analyticAt hza
  have hev : ∀ᶠ u in 𝓝 (0:ℂ),AnalyticAt ℂ zeta u ∧ AnalyticAt ℂ (negativeChartRoot lam zeta) u ∧
      0<(negativeChartB lam zeta u).im ∧ spectralS (zeta u)≠0 ∧ negativeChartRoot lam zeta u≠0 ∧ ‖u‖<r₀ := by
    filter_upwards [hza.eventually_analyticAt,hAa.eventually_analyticAt,
      (Complex.continuous_im.continuousAt.comp hBa.continuousAt).eventually_const_lt hB0,
      hSa.continuousAt.eventually_ne hS,hAa.continuousAt.eventually_ne hA0,ball_mem_nhds (0:ℂ) hr₀]
      with u hz ha hb hs hr hu
    exact ⟨hz,ha,hb,hs,hr,by simpa only [mem_ball,dist_zero_right] using hu⟩
  obtain ⟨r,hr,hrsub⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨r,hr,fun u hu => (hrsub hu).1,fun u hu => (hrsub hu).2.1,?_⟩
  intro u hu
  obtain ⟨_,_,hb,hs,hA,hur⟩ := hrsub hu
  obtain ⟨he,hin⟩ := hchart u hur
  refine ⟨hb,hs,hA,he,fun hi => ⟨hin hi,?_⟩⟩
  intro hzero
  apply hs
  simp only [Set.mem_singleton_iff.mp hzero,spectralS,Complex.sinh_zero]

theorem negative_low_prime_raw_chart_no_extension {lam b : ℝ} {D : Set ℂ} {zeta : ℂ→ℂ} {r : ℝ}
    (hlam : 0<lam) (hb : |b|<1) (hprime : b∈primePhaseCosines) (hr : 0<r)
    (hza : AnalyticOnNhd ℂ zeta (ball 0 r))
    (hAa : AnalyticOnNhd ℂ (negativeChartRoot lam zeta) (ball 0 r))
    (hd : spectralDet lam (zeta 0)<0)
    (hphysical : D⊆omegaH lam∪omegaL lam)
    (hdata : ∀u∈ball 0 r,0<(negativeChartB lam zeta u).im ∧ spectralS (zeta u)≠0 ∧
      negativeChartRoot lam zeta u≠0 ∧ edgeMapV lam (-1) (zeta u)=(b:ℂ)+u ∧
      (0<u.im → zeta u∈D\{0})) :
    ¬HasDomainExtension (upperBall r) (fun u => ∑'i,
      (spectralProduct lam (zeta u))^(i+1)*unscaledFullCoefficient (2*i+2) lam (zeta u)) 0 := by
  have h0 : (0:ℂ)∈ball 0 r := mem_ball_self hr
  have hz0 := hza 0 h0
  have hS0 := (hdata 0 h0).2.1
  have hP0 : spectralProduct lam (zeta 0)≠0 :=
    mul_ne_zero hS0 (spectralT_ne_zero_of_det_ne_zero hd.ne)
  have hpU : ∀u∈upperBall r,zeta u∈(omegaH lam\{0})∪omegaL lam := by
    intro u hu
    have hD := (hdata u hu.1).2.2.2.2 hu.2
    rcases hphysical hD.1 with hH | hL
    · exact Or.inl ⟨hH,hD.2⟩
    · exact Or.inr hL
  have hz : ∀u∈upperBall r,zeta u∉spectralSet lam := by
    intro u hu
    rcases hpU u hu with hH | hL
    · exact omegaH_subset_spectral_complement hlam hH.1
    · exact omegaL_subset_spectral_complement hlam hL
  have hAsq : ∀u∈upperBall r,negativeChartRoot lam zeta u^2=spectralProduct lam (zeta u) :=
    fun u _ => localParticleRoot_sq hP0 u
  have hBa := negativeChartB_analyticAt (lam := lam) hz0 hS0
  have hSa := negativeChartS_analyticAt hz0
  exact negative_low_prime_chart_no_extension (upperBall_isOpen r) (hza.mono inter_subset_left)
      (hAa.mono inter_subset_left) hz (fun u hu => (hdata u hu.1).2.1)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun u hu => (hdata u hu.1).2.2.2.1)
      (fun _ hu => hu.2) (fun u hu => (hdata u hu.1).1) hlam hpU hb hBa (hdata 0 h0).1
      hSa hS0 hz0 (hAa 0 h0) (hdata 0 h0).2.2.1 hP0 hAsq (upperBall_inward hr) hprime


/-- Actual negative V-endpoint obstruction for the complete physical LT bulk,
including its normalized physical fourth-root prefactor. -/
theorem low_negative_prime_no_extension {lam : ℝ} (hlam : 0<lam) {z : ℂ}
    (hz : z∈frontier (omegaL lam)) (hd : spectralDet lam z<0)
    (hv : spectralV lam z= -1) (hu : |spectralU lam z|<1)
    (hder : deriv (edgeMapV lam (-1)) z≠0) (hprime : spectralU lam z∈primePhaseCosines) :
    ¬HasDomainExtension (omegaL lam) (lowNormalizedBulk lam) z := by
  obtain ⟨zeta,hζa,hζ0,r₀,hr₀,hchart⟩ := exists_oriented_V_low_chart hlam hz hd.ne
    (Or.inr rfl : (-1:ℝ)=1 ∨ (-1:ℝ)= -1) hv hu (by simpa only [Complex.ofReal_neg,Complex.ofReal_one] using hder) (by simpa using neg_pos.mpr hd)
  simp only [Complex.ofReal_neg,Complex.ofReal_one] at hchart
  have hdζ : spectralDet lam (zeta 0)<0 := by rw [hζ0]; exact hd
  obtain ⟨r,hr,haζ,hAa,hdata⟩ := exists_negative_general_chart_data hζa hdζ hr₀ hchart
  have hP0 : spectralProduct lam (zeta 0)≠0 :=
    mul_ne_zero (spectralS_ne_zero_of_det_ne_zero hdζ.ne) (spectralT_ne_zero_of_det_ne_zero hdζ.ne)
  have hPa : AnalyticAt ℂ (fun u => spectralProduct lam (zeta u)) 0 :=
    (spectralProduct_analyticAt_ff lam _).comp hζa
  have hQa : AnalyticAt ℂ (fun u => 1-(spectralProduct lam (zeta u))⁻¹^2) 0 :=
    analyticAt_const.sub ((hPa.inv hP0).pow 2)
  have hQ0 : 1-(spectralProduct lam (zeta 0))⁻¹^2≠0 := by
    intro h
    have hh : ((spectralProduct lam (zeta 0))^2)⁻¹=1 := by
      simpa only [inv_pow] using (sub_eq_zero.mp h).symm
    have hp := inv_eq_one.mp hh
    rw [hζ0] at hp
    exact product_sq_ne_one_of_strictU hd.ne hu hp
  have hmap : MapsTo zeta (upperBall r) (omegaL lam) :=
    fun u hu => ((hdata u hu.1).2.2.2.2 hu.2).1
  have hfc : ContinuousOn (fun u => lowPrefactor lam (zeta u)) (upperBall r) := by
    intro u hu
    exact (((lowPrefactor_actual_spec hlam).1 _ (hmap hu)).continuousAt.comp
      (haζ u hu.1).continuousAt).continuousWithinAt
  have hfp : ∀u∈upperBall r,(lowPrefactor lam (zeta u))^4=1-(spectralProduct lam (zeta u))⁻¹^2 :=
    fun u hu => (lowPrefactor_actual_spec hlam).2.1 _ (hmap hu)
  have hraw : ∀δ : ℝ,0<δ → δ≤r → ¬HasDomainExtension (upperBall δ) (fun u => ∑'i,
      (spectralProduct lam (zeta u))^(i+1)*unscaledFullCoefficient (2*i+2) lam (zeta u)) 0 := by
    intro δ hδ hδr
    exact negative_low_prime_raw_chart_no_extension hlam hu hprime hδ
      (haζ.mono (ball_subset_ball hδr)) (hAa.mono (ball_subset_ball hδr)) hdζ
      (fun _ h => Or.inr h) (fun u hu => hdata u (ball_subset_ball hδr hu))
  have hno := no_extension_product_of_upper_fourth_branch hr hQa hQ0 hfc hfp hraw
  intro hext
  apply hno
  simpa only [Function.comp_apply,lowNormalizedBulk] using!
    domain_extension_comp_of_mapsTo hζa hζ0 hmap hext

end
end IsingBulk.Anisotropic.RegularEdges
