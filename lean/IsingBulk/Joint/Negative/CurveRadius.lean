import IsingBulk.Joint.Negative.CurveBounds
import IsingBulk.Joint.Negative.CoefficientRadius
import IsingBulk.Anisotropic.NegativeDominance.PrimeNegativePhase

/-! Zero Taylor radius of the complete, genuinely variable-anisotropy negative
odd coefficient series. Only analytic curve data and the rational edge phase
are inputs; all particle/winding estimates are constructed inside the proof. -/
namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter IsingBulk.Anisotropic
open IsingBulk.Anisotropic.RegularEdges IsingBulk.Anisotropic.NegativeDominance
open scoped Topology BigOperators
set_option maxHeartbeats 2000000

/-- Complete negative-edge coefficient zero radius for an arbitrary normalized
holomorphic curve in the two independent complex couplings. No Cauchy bound,
normal-form witness, dominance estimate, or radius premise is assumed. -/
theorem normalized_negative_curve_radius_zero {curve : ℂ→Coupling} {amp : ℂ→ℂ} {b : ℝ}
    (hc : AnalyticAt ℂ curve 0) (ha : AnalyticAt ℂ amp 0)
    (hs : S (curve 0)≠0) (hB : (transferB (curve 0)).im<0)
    (hprime : b∈primePhaseCosines)
    (he : ∀ᶠt in 𝓝 (0:ℂ),transferC (curve t)+transferB (curve t)=
      (b:ℂ)+transferB (curve t)*t)
    (hsq : ∀ᶠt in 𝓝 (0:ℂ),amp t^2=p (curve t)) :
    (FormalMultilinearSeries.ofScalars ℂ (negativePaperCoefficient curve amp)).radius=0 := by
  obtain ⟨p0,phi,hp,hpo,hphi0,hphipi,hphi,hcos,hphase,hres⟩ := exists_prime_negative_phase hprime
  have hb0 : transferB (curve 0)≠0 := transferB_ne_zero_of_im_neg hB
  have ht : T (curve 0)≠0 := by
    intro h
    apply hb0
    simp [transferB,h]
  have hp0 : p (curve 0)≠0 := mul_ne_zero hs ht
  have ha0 : amp 0≠0 := by
    intro h
    have hq := hsq.self_of_nhds
    rw [h,zero_pow (by decide : (2:ℕ)≠0)] at hq
    exact hp0 hq.symm
  obtain ⟨D⟩ := exists_upperNormalization hc ha hs ha0 hB he hsq
  have hb : |b|<1 := by
    rw [hcos]
    exact (sq_lt_one_iff_abs_lt_one _).mp (by
      nlinarith [Real.sin_sq_add_cos_sq phi,sq_pos_of_ne_zero hphi])
  obtain ⟨⟨a,Dlow,aR,CR,haR,hDlow,haRR,hlow,hnonres⟩,houter⟩ := D.actual_bounds hb hp.two_le hphase
  obtain ⟨hBa,hB0,hrB,hr0,hrsq⟩ := paper_model_data hc ha hs ht ha0 hsq
  have hedge : A (curve 0)+T (curve 0)=(Real.cos phi:ℂ)*S (curve 0) := by
    have h := he.self_of_nhds
    rw [mul_zero,add_zero,hcos] at h
    dsimp only [transferC,transferB] at h
    field_simp at h
    linear_combination h
  have hBi : 0<(-T (curve 0)/S (curve 0)).im := by
    simpa only [neg_div,Complex.neg_im,transferB,neg_pos] using hB
  have hS := (negativeChartS_analyticAt hc).continuousAt.eventually_ne hs
  have hchart : ∀ᶠt in 𝓝 (0:ℂ),S (curve t)≠0 ∧
      paperModelB curve t=T (curve t)/S (curve t) ∧
      transferC (curve t)+transferB (curve t)=(Real.cos phi:ℂ)+paperModelB curve t*t ∧
      amp t^2=p (curve t) ∧ amp t/S (curve t)=paperModelRoot curve amp t := by
    filter_upwards [hS,he,hsq] with t hst het hqt
    exact ⟨hst,rfl,by simpa only [hcos,paperModelB] using het,hqt,rfl⟩
  exact actual_negative_paper_radius_zero (paperModelB curve) (paperModelRoot curve amp)
    phi hphi hphi0 hphipi hBa hB0 hrB hr0 hrsq curve amp hc ha hs hedge
    (by simpa only [hcos] using hb) hBi hchart houter p0 hp.pos hpo
    (fun m hm=>hres (2*m+1) hm) a Dlow aR CR haR hDlow.le haRR hlow hnonres

end
end IsingBulk.Joint.Negative
