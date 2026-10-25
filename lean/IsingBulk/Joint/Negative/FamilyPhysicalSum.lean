import IsingBulk.Joint.Negative.FamilyHighTube
import IsingBulk.Joint.Negative.PhysicalBoundaryJets

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
set_option maxHeartbeats 1600000

/-- The actual complete weighted physical high-temperature series. -/
def weightedPhysicalHigh (curve : ℂ→Coupling) (amp : ℂ→ℂ) (t : ℂ) : ℂ :=
  amp t*∑'n : ℕ,p (curve t)^n*FormFactors.unscaledFullCoefficient (2*n+1) (curve t)

/-- Exact relation to the normalized physical susceptibility, not a formal
angular proxy. The physical prefactor is retained as an analytic unit. -/
theorem weightedPhysicalHigh_eq_normalized (curve : ℂ→Coupling) (amp : ℂ→ℂ) :
    weightedPhysicalHigh curve amp=fun t=>amp t/FormFactors.highPrefactor (curve t)*
      FormFactors.highNormalizedBulk (curve t) := by
  funext t
  unfold weightedPhysicalHigh FormFactors.highNormalizedBulk
  field_simp [FormFactors.highPrefactor_ne_zero]

theorem negative_high_weighted_particle_eq (m : ℕ) {K : Coupling} {a : ℂ} {b : ℝ}
    (hK : K∈highDomain) (hS : S K≠0) (hB : (transferB K).im<0)
    (hi : 0<(transferC K+transferB K-(b:ℂ)).im) (ha : a^2=p K) :
    a*(p K^m*FormFactors.unscaledFullCoefficient (2*m+1) K)=
      a^(2*m+1)*continuedAngularCoefficient (2*m) K := by
  have hw : ∀q : ℝ,0<(transferW K (q:ℂ)).im :=
    transferW_im_pos_negative_chart (B:=fun _=>-T K/S K) rfl
      (by ring) hi (by simpa only [neg_div,Complex.neg_im,neg_pos,transferB] using hB)
  rw [RegularEdges.fullCoefficient_eq_physicalAngular_high (2*m) hK hS,
    ←continuedAngularCoefficient_eq_unscaled_of_im_pos (2*m)
      (highDomain_subset_spectralComplement hK) hS hw,←ha,←pow_mul,pow_succ]
  ring

/-- Every interior full-series derivative equals the sum of the literal
continued odd coefficient derivatives on one common inward tube. Physical
component membership and the square identity are derived uniformly. -/
theorem compact_negative_high_weighted_jets_identity {Q : Set E}
    (curve : ℂ × E→Coupling) (amp : ℂ × E→ℂ) {b : ℝ}
    (hQ : IsCompact Q) (hc : ∀eta∈Q,AnalyticAt ℂ curve (0,eta))
    (ha : ∀eta∈Q,AnalyticAt ℂ amp (0,eta))
    (hS : ∀eta∈Q,S (curve (0,eta))≠0)
    (hB : ∀eta∈Q,(transferB (curve (0,eta))).im<0)
    (hK : ∀eta∈Q,curve (0,eta)∈frontier highDomain)
    (hp : ∀eta∈Q,p (curve (0,eta))^2≠1) (hb : |b|<1)
    (he : ∀eta∈Q,∀ᶠt : ℂ in 𝓝 0,transferC (curve (t,eta))+transferB (curve (t,eta))=
      (b:ℂ)+transferB (curve (t,eta))*t)
    (hsq : ∀eta∈Q,∀ᶠt : ℂ in 𝓝 0,amp (t,eta)^2=p (curve (t,eta))) :
    ∃r : ℝ,0<r ∧ ∀eta∈Q,∀ε : ℝ,0<ε → ε<r → ∀j : ℕ,
      HasSum (fun n=>iteratedDeriv j
        (fun t=>amp (t,eta)^(2*n+1)*continuedAngularCoefficient (2*n) (curve (t,eta))) (-(ε:ℂ)))
        (iteratedDeriv j (weightedPhysicalHigh (fun t=>curve (t,eta)) (fun t=>amp (t,eta))) (-(ε:ℂ))) := by
  obtain ⟨a,ha0,htube⟩ := compact_negative_high_tube curve hQ hc hS hB hK hp hb he
  obtain ⟨d,M,hd,_hM,hamp⟩ := compact_analytic_uniform_bound amp hQ ha
  obtain ⟨c,hc0,hsquare⟩ := compact_family_analytic_identity
    (fun q=>amp q^2) (fun q=>p (curve q)) hQ
    (fun eta heta=>(ha eta heta).pow 2)
    (fun eta heta=>(FormFactors.p_analyticAt_normalized _).comp (hc eta heta)) hsq
  let r := min a (min d c)
  have hr : 0<r := lt_min ha0 (lt_min hd hc0)
  refine ⟨r,hr,?_⟩
  intro eta heta ε hε hεr j
  let x : ℂ := -(ε:ℂ)
  have hxn : ‖x‖<r := by simpa only [x,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hε] using hεr
  have hxdata := htube eta heta x (hxn.trans_le (min_le_left _ _))
  have hxamp := (hamp eta heta x (hxn.trans_le ((min_le_right _ _).trans (min_le_left _ _)))).1
  have hxpos : 0<(transferB (curve (x,eta))*x).im := by
    simpa only [x,Complex.mul_im,Complex.neg_re,Complex.ofReal_re,Complex.neg_im,Complex.ofReal_im,
      neg_zero,mul_zero,zero_add] using mul_pos_of_neg_of_neg hxdata.2.2.1 (neg_neg_of_pos hε)
  have hxhigh := hxdata.2.2.2.2.mpr hxpos
  have hcx : AnalyticAt ℂ (fun t=>curve (t,eta)) x :=
    hxdata.1.comp (f:=fun t : ℂ=>(t,eta)) (analyticAt_id.prod analyticAt_const)
  have hax : AnalyticAt ℂ (fun t=>amp (t,eta)) x :=
    hxamp.comp (f:=fun t : ℂ=>(t,eta)) (analyticAt_id.prod analyticAt_const)
  have hpos : 0<(transferC (curve (x,eta))+transferB (curve (x,eta))-(b:ℂ)).im := by
    simpa only [hxdata.2.2.2.1,add_sub_cancel_left] using hxpos
  have hpa : AnalyticAt ℂ (fun t=>transferC (curve (t,eta))+transferB (curve (t,eta))-(b:ℂ)) x :=
    (((transferC_analyticAt hxdata.2.1).comp (f:=fun t : ℂ=>curve (t,eta)) hcx).add
      ((transferB_analyticAt hxdata.2.1).comp (f:=fun t : ℂ=>curve (t,eta)) hcx)).sub analyticAt_const
  have hgerm (n : ℕ) :
      (fun t=>amp (t,eta)*(p (curve (t,eta))^n*FormFactors.unscaledFullCoefficient (2*n+1) (curve (t,eta)))) =ᶠ[𝓝 x]
      (fun t=>amp (t,eta)^(2*n+1)*continuedAngularCoefficient (2*n) (curve (t,eta))) := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hxn),
      continuousAt_const.eventually_lt (Complex.continuous_im.continuousAt.comp hpa.continuousAt) hpos] with t htr hti
    dsimp only [Function.comp_apply] at hti
    have htn : ‖t‖<r := mem_ball_zero_iff.mp htr
    have htdata := htube eta heta t (htn.trans_le (min_le_left _ _))
    have htpos : 0<(transferB (curve (t,eta))*t).im := by
      simpa only [htdata.2.2.2.1,add_sub_cancel_left] using hti
    exact negative_high_weighted_particle_eq n (htdata.2.2.2.2.mpr htpos) htdata.2.1 htdata.2.2.1 hti
      (hsquare eta heta t (htn.trans_le ((min_le_right _ _).trans (min_le_right _ _))))
  have hfull := FormFactors.high_particleSeries_mul_comp_hasSum_iteratedDeriv hcx hax
    (highDomain_subset_spectralComplement hxhigh) j
  have heq : (fun n=>iteratedDeriv j
      (fun t=>amp (t,eta)*(p (curve (t,eta))^n*FormFactors.unscaledFullCoefficient (2*n+1) (curve (t,eta)))) x)=
      (fun n=>iteratedDeriv j
        (fun t=>amp (t,eta)^(2*n+1)*continuedAngularCoefficient (2*n) (curve (t,eta))) x) :=
    funext (fun n=>(hgerm n).iteratedDeriv_eq j)
  rw [heq] at hfull
  exact hfull

end
end IsingBulk.Joint.Negative
