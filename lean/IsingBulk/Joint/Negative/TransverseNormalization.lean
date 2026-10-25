import IsingBulk.Joint.Negative.CurveRadius
import IsingBulk.Joint.Transverse.CurveCoordinates

/-! Every nonramified transverse curve is normalized in its actual negative
edge coordinate, with its variable complex anisotropy preserved. -/
namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter
open scoped Topology

theorem edgeParameter_curve_analyticAt {curve : ℂ→Coupling} {z : ℂ} (b : ℂ)
    (hc : AnalyticAt ℂ curve z) (hS : S (curve z)≠0) (hB : transferB (curve z)≠0) :
    AnalyticAt ℂ (fun t=>edgeParameter b (curve t)) z := by
  have hA : AnalyticAt ℂ (fun t=>A (curve t)) z :=
    (Complex.analyticAt_cosh.comp (analyticAt_fst.comp hc)).mul
      (Complex.analyticAt_cosh.comp (analyticAt_snd.comp hc))
  have hSa : AnalyticAt ℂ (fun t=>S (curve t)) z :=
    Complex.analyticAt_sinh.comp (analyticAt_fst.comp hc)
  exact (((hA.div hSa hS).add (curveB_analyticAt hc hS)).sub analyticAt_const).div
    (curveB_analyticAt hc hS) hB

theorem normalize_negative_curve {curve : ℂ→Coupling} {z : ℂ} {b : ℝ}
    (hc : AnalyticAt ℂ curve z) (hS : S (curve z)≠0)
    (hB : (transferB (curve z)).im<0)
    (he : edgeParameter b (curve z)=0)
    (hd : deriv (fun t=>edgeParameter b (curve t)) z≠0) :
    ∃psi : ℂ→ℂ,∃normalized : ℂ→Coupling,
      AnalyticAt ℂ psi 0 ∧ psi 0=z ∧ normalized=curve∘psi ∧
      AnalyticAt ℂ normalized 0 ∧ normalized 0=curve z ∧
      (∀ᶠt in 𝓝 (0:ℂ),transferC (normalized t)+transferB (normalized t)=
        (b:ℂ)+transferB (normalized t)*t) ∧
      (∀ᶠu in 𝓝 z,psi (edgeParameter b (curve u))=u) := by
  have hB0 := transferB_ne_zero_of_im_neg hB
  obtain ⟨psi,hpa,hp0,hpr,hpl⟩ := Transverse.exists_nonramified_inverse
    (edgeParameter_curve_analyticAt b hc hS hB0) he hd
  have hca : AnalyticAt ℂ (curve∘psi) 0 := hc.comp_of_eq hpa hp0
  have hBca := curveB_analyticAt hca (by simpa only [Function.comp_apply,hp0] using hS)
  refine ⟨psi,curve∘psi,hpa,hp0,rfl,hca,by simp [hp0],?_,hpl⟩
  filter_upwards [hpr,hBca.continuousAt.eventually_ne (by
    simpa only [curveB,Function.comp_apply,hp0] using hB0)] with t ht hBt
  have h := edgeParameter_identity b ((curve∘psi) t) hBt
  simp only [Function.comp_apply] at h ⊢
  rw [ht] at h
  exact h

/-- On every transverse curve the constructed normalized complete odd series
has zero Taylor radius. No direction is fixed and B is allowed to vary. -/
theorem transverse_negative_curve_zero_radius {curve : ℂ→Coupling} {z : ℂ} {b : ℝ}
    (hc : AnalyticAt ℂ curve z) (hS : S (curve z)≠0)
    (hB : (transferB (curve z)).im<0)
    (he : edgeParameter b (curve z)=0)
    (hd : deriv (fun t=>edgeParameter b (curve t)) z≠0)
    (hprime : b∈IsingBulk.Anisotropic.primePhaseCosines) :
    ∃psi : ℂ→ℂ,∃normalized : ℂ→Coupling,∃amp : ℂ→ℂ,
      AnalyticAt ℂ psi 0 ∧ psi 0=z ∧ normalized=curve∘psi ∧
      AnalyticAt ℂ normalized 0 ∧ AnalyticAt ℂ amp 0 ∧ amp 0≠0 ∧
      (∀t,amp t^2=p (normalized t)) ∧
      (∀ᶠu in 𝓝 z,psi (edgeParameter b (curve u))=u) ∧
      (FormalMultilinearSeries.ofScalars ℂ (negativePaperCoefficient normalized amp)).radius=0 := by
  obtain ⟨psi,N,hpa,hp0,hN,hNa,hN0,hchart,hpl⟩ := normalize_negative_curve hc hS hB he hd
  have hSN : S (N 0)≠0 := by rwa [hN0]
  have hBN : (transferB (N 0)).im<0 := by rwa [hN0]
  have hTN : T (N 0)≠0 := by
    intro h
    have hh := transferB_ne_zero_of_im_neg hBN
    exact hh (by simp [transferB,h])
  have hP : p (N 0)≠0 := mul_ne_zero hSN hTN
  have hAa := negativeChartRoot_analyticAt hNa hP
  have hA0 : negativeChartRoot N 0≠0 := IsingBulk.Anisotropic.RegularEdges.localParticleRoot_ne_zero hP
  refine ⟨psi,N,negativeChartRoot N,hpa,hp0,hN,hNa,hAa,hA0,negativeChartRoot_sq hP,hpl,?_⟩
  exact normalized_negative_curve_radius_zero hNa hAa hSN hBN hprime hchart
    (Eventually.of_forall (negativeChartRoot_sq hP))

end
end IsingBulk.Joint.Negative
