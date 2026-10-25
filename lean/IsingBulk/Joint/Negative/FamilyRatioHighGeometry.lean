import IsingBulk.Joint.Negative.FamilyRatioObstruction
import IsingBulk.Joint.Negative.FamilyHighTube

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric
open FormFactors
open scoped Topology
set_option maxHeartbeats 1600000

/-- The constructed complex-ratio family can be shrunk once so that every
complex parameter center is on the actual noncritical high-temperature face.
This is derived from the original component closure and flat-face geometry. -/
theorem negative_ratio_common_high_centers {b : ℝ} {z₀ lam₀ : ℂ} {outerAmp : Coupling→ℂ}
    (F : ComplexRatioFamily (edgeParameter (b:ℂ)) outerAmp (-1) z₀ lam₀)
    (hK : (z₀,lam₀*z₀)∈closure highDomain) (hp : p (z₀,lam₀*z₀)^2≠1) (hb : |b|<1) :
    ∃ρ : ℝ,0<ρ ∧ ρ≤F.radius ∧ ∀lam∈closedBall lam₀ ρ,
      F.coupling (0,lam)∈frontier highDomain ∧ p (F.coupling (0,lam))^2≠1 := by
  have h0 : (0,lam₀)∈F.polydisk := F.zero_mem_polydisk (mem_closedBall_self F.radius_pos.le)
  have hc0 : AnalyticAt ℂ F.coupling (0,lam₀) :=
    F.coupling_analytic 0 lam₀ (F.polydisk_bounds h0).1 (F.polydisk_bounds h0).2
  have hS0 : S (z₀,lam₀*z₀)≠0 := by simpa only [ComplexRatioFamily.scale,F.coupling_zero] using F.scale_ne_zero h0
  have hB0 : 0<(-transferB (z₀,lam₀*z₀)).im := by
    have hh := F.anisotropy_sign h0
    simpa only [ComplexRatioFamily.anisotropy,F.coupling_zero,neg_one_mul,Complex.neg_im] using hh
  have he0 : Transverse.negativeParameter b (z₀,lam₀*z₀)=0 := by
    have hh := (negative_ratio_actual_chart F h0).2.2.1
    simpa only [Transverse.negativeParameter,F.coupling_zero,mul_zero,add_zero,sub_self] using
      congrArg (fun z : ℂ=>z-(b:ℂ)) hh
  obtain ⟨U,hU,hKU,_hface,hside⟩ := Transverse.negativeFace_domain_side hK
    highDomain_subset_spectralComplement highDomain_component hS0 hp hB0 hb he0
  have hpcont : ContinuousAt (fun q=>p (F.coupling q)^2) (0,lam₀) :=
    ((FormFactors.p_analyticAt_normalized _).comp hc0).continuousAt.pow 2
  have hev : ∀ᶠq in 𝓝 (0,lam₀),F.coupling q∈U ∧ p (F.coupling q)^2≠1 := by
    have hu : ∀ᶠq in 𝓝 (0,lam₀),F.coupling q∈U :=
      hc0.continuousAt.preimage_mem_nhds (by simpa only [F.coupling_zero] using hU.mem_nhds hKU)
    exact hu.and (hpcont.eventually_ne (by simpa only [F.coupling_zero] using hp))
  obtain ⟨δ,hδ,hδmem⟩ := Metric.eventually_nhds_iff.mp hev
  let ρ := min (δ/2) F.radius
  have hρ : 0<ρ := lt_min (half_pos hδ) F.radius_pos
  have hρF : ρ≤F.radius := min_le_right _ _
  have hall (t lam : ℂ) (ht : ‖t‖≤ρ) (hl : lam∈closedBall lam₀ ρ) :
      (t,lam)∈F.polydisk ∧ F.coupling (t,lam)∈U ∧ p (F.coupling (t,lam))^2≠1 := by
    have hl' : ‖lam-lam₀‖≤ρ := by simpa only [mem_closedBall,dist_eq_norm] using hl
    have hdist : dist (t,lam) (0,lam₀)<δ := by
      simp only [dist_eq_norm,Prod.mk_sub_mk,Prod.norm_def,sub_zero,max_lt_iff]
      exact ⟨ht.trans_lt ((min_le_left _ _).trans_lt (half_lt_self hδ)),
        hl'.trans_lt ((min_le_left _ _).trans_lt (half_lt_self hδ))⟩
    exact ⟨⟨mem_closedBall_zero_iff.mpr (ht.trans hρF),
      by simpa only [mem_closedBall,dist_eq_norm] using hl'.trans hρF⟩,hδmem hdist⟩
  refine ⟨ρ,hρ,hρF,?_⟩
  intro lam hl
  have hc := hall 0 lam (by simpa only [norm_zero] using hρ.le) hl
  refine ⟨?_,hc.2.2⟩
  have hedge : Transverse.negativeParameter b (F.coupling (0,lam))=0 := by
    have hh := (negative_ratio_actual_chart F hc.1).2.2.1
    simp only [mul_zero,add_zero] at hh
    simp only [Transverse.negativeParameter,hh,sub_self]
  have hca : AnalyticAt ℂ (fun t : ℂ=>F.coupling (t,lam)) 0 :=
    (F.coupling_analytic 0 lam (F.polydisk_bounds hc.1).1 (F.polydisk_bounds hc.1).2).comp
      (f:=fun t : ℂ=>(t,lam)) (analyticAt_id.prod analyticAt_const)
  have hlim : Tendsto (fun ε : ℝ=>F.coupling (-(ε:ℂ),lam)) (𝓝[>] 0) (𝓝 (F.coupling (0,lam))) := by
    have hpath : Tendsto (fun ε : ℝ=>-(ε:ℂ)) (𝓝[>] 0) (𝓝 0) := by
      have ht : Tendsto (fun ε : ℝ=>-(ε:ℂ)) (𝓝[>] (0:ℝ)) (𝓝 (-((0:ℝ):ℂ))) :=
        (show ContinuousAt (fun ε : ℝ=>-(ε:ℂ)) 0 from
          Complex.continuous_ofReal.neg.continuousAt).tendsto.mono_left nhdsWithin_le_nhds
      simpa only [Complex.ofReal_zero,neg_zero] using ht
    exact hca.continuousAt.tendsto.comp hpath
  have hin : ∀ᶠε : ℝ in 𝓝[>] 0,F.coupling (-(ε:ℂ),lam)∈highDomain := by
    filter_upwards [Ioo_mem_nhdsGT hρ] with ε hε
    have hh := hall (-(ε:ℂ)) lam (by simpa [abs_of_pos hε.1] using hε.2.le) hl
    apply (hside _ hh.2.1).mpr
    have hchart := (negative_ratio_actual_chart F hh.1).2.2.1
    have hsign : (F.anisotropy (-(ε:ℂ),lam)).im<0 := by
      simpa only [neg_one_mul,neg_pos] using F.anisotropy_sign hh.1
    rw [Transverse.negativeParameter,hchart,add_sub_cancel_left]
    simpa only [Complex.mul_im,Complex.neg_re,Complex.ofReal_re,Complex.neg_im,Complex.ofReal_im,
      neg_zero,mul_zero,zero_add] using mul_pos_of_neg_of_neg hsign (neg_neg_of_pos hε.1)
  rw [highDomain_isOpen.frontier_eq]
  refine ⟨mem_closure_of_tendsto hlim hin,?_⟩
  intro hin
  have hh := (hside _ hc.2.1).mp hin
  simp only [hedge,Complex.zero_im,lt_self_iff_false] at hh

end
end IsingBulk.Joint.Negative
