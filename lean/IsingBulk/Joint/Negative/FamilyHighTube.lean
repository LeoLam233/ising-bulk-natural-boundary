import IsingBulk.Joint.Negative.FamilyChartIdentity
import IsingBulk.Joint.Transverse.NegativeLocalSide

namespace IsingBulk.Joint.Negative
noncomputable section
open Set Filter Metric
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
set_option maxHeartbeats 1200000

/-- Actual high-domain side on a common complex tube around every member of a
compact normalized negative-edge family. No physical-side map is assumed. -/
theorem compact_negative_high_tube {Q : Set E} (curve : ℂ × E→Coupling) {b : ℝ}
    (hQ : IsCompact Q) (hc : ∀eta∈Q,AnalyticAt ℂ curve (0,eta))
    (hS : ∀eta∈Q,S (curve (0,eta))≠0)
    (hB : ∀eta∈Q,(transferB (curve (0,eta))).im<0)
    (hK : ∀eta∈Q,curve (0,eta)∈frontier highDomain)
    (hp : ∀eta∈Q,p (curve (0,eta))^2≠1) (hb : |b|<1)
    (he : ∀eta∈Q,∀ᶠt : ℂ in 𝓝 0,transferC (curve (t,eta))+transferB (curve (t,eta))=
      (b:ℂ)+transferB (curve (t,eta))*t) :
    ∃r : ℝ,0<r ∧ ∀eta∈Q,∀t : ℂ,‖t‖<r →
      AnalyticAt ℂ curve (t,eta) ∧ S (curve (t,eta))≠0 ∧
      (transferB (curve (t,eta))).im<0 ∧
      transferC (curve (t,eta))+transferB (curve (t,eta))=(b:ℂ)+transferB (curve (t,eta))*t ∧
      (curve (t,eta)∈highDomain ↔ 0<(transferB (curve (t,eta))*t).im) := by
  let V : Set (ℂ × E) := interior {q | curve q∈highDomain ↔
    0<(Transverse.negativeParameter b (curve q)).im}
  have hV (eta : E) (heta : eta∈Q) : (0,eta)∈V := by
    obtain ⟨U,hU,hKU,_hface,hside⟩ := Transverse.negativeFace_high_side
      (hK eta heta) (hS eta heta) (hp eta heta)
      (by simpa only [Complex.neg_im,neg_pos] using hB eta heta) hb
      (by have hh := (he eta heta).self_of_nhds
          simp only [mul_zero,add_zero] at hh
          simp only [Transverse.negativeParameter,hh,sub_self])
    apply mem_interior_iff_mem_nhds.mpr
    filter_upwards [(hc eta heta).continuousAt.tendsto.eventually (hU.mem_nhds hKU)] with q hq
    exact hside _ hq
  let U : Set (ℂ × E) := {q | AnalyticAt ℂ curve q ∧ S (curve q)≠0 ∧ (transferB (curve q)).im<0} ∩ V
  have hU : IsOpen U := by
    apply IsOpen.inter _ isOpen_interior
    rw [isOpen_iff_mem_nhds]
    intro q hq
    have hs : AnalyticAt ℂ (fun q=>S (curve q)) q :=
      Complex.analyticAt_sinh.comp (analyticAt_fst.comp hq.1)
    have hbc := ((transferB_analyticAt hq.2.1).comp hq.1).continuousAt
    exact hq.1.eventually_analyticAt.and ((hs.continuousAt.eventually_ne hq.2.1).and
      ((Complex.continuous_im.continuousAt.comp hbc).eventually_lt continuousAt_const hq.2.2))
  obtain ⟨a,ha,htube⟩ := compact_product_tube hQ hU
    (fun eta heta=>⟨⟨hc eta heta,hS eta heta,hB eta heta⟩,hV eta heta⟩)
  obtain ⟨c,hc0,hident⟩ := compact_family_analytic_identity
    (fun q=>transferC (curve q)+transferB (curve q))
    (fun q=>(b:ℂ)+transferB (curve q)*q.1) hQ
    (fun eta heta=>((transferC_analyticAt (hS eta heta)).comp (hc eta heta)).add
      ((transferB_analyticAt (hS eta heta)).comp (hc eta heta)))
    (fun eta heta=>analyticAt_const.add
      (((transferB_analyticAt (hS eta heta)).comp (hc eta heta)).mul analyticAt_fst)) he
  refine ⟨min a c,lt_min ha hc0,?_⟩
  intro eta heta t ht
  have hu := htube eta heta t (ht.trans_le (min_le_left _ _))
  have hi := hident eta heta t (ht.trans_le (min_le_right _ _))
  refine ⟨hu.1.1,hu.1.2.1,hu.1.2.2,hi,?_⟩
  have hv := interior_subset hu.2
  change curve (t,eta)∈highDomain ↔ 0<(Transverse.negativeParameter b (curve (t,eta))).im at hv
  simpa only [Transverse.negativeParameter,hi,add_sub_cancel_left] using hv

/-- Every negative-real transverse approach enters the actual high component
on the same radius for all complex parameters in the compact set. -/
theorem compact_negative_high_real_approach {Q : Set E} (curve : ℂ × E→Coupling) {b : ℝ}
    (hQ : IsCompact Q) (hc : ∀eta∈Q,AnalyticAt ℂ curve (0,eta))
    (hS : ∀eta∈Q,S (curve (0,eta))≠0)
    (hB : ∀eta∈Q,(transferB (curve (0,eta))).im<0)
    (hK : ∀eta∈Q,curve (0,eta)∈frontier highDomain)
    (hp : ∀eta∈Q,p (curve (0,eta))^2≠1) (hb : |b|<1)
    (he : ∀eta∈Q,∀ᶠt : ℂ in 𝓝 0,transferC (curve (t,eta))+transferB (curve (t,eta))=
      (b:ℂ)+transferB (curve (t,eta))*t) :
    ∃r : ℝ,0<r ∧ ∀eta∈Q,∀ε : ℝ,0<ε → ε<r →
      AnalyticAt ℂ curve (-(ε:ℂ),eta) ∧ S (curve (-(ε:ℂ),eta))≠0 ∧
      curve (-(ε:ℂ),eta)∈highDomain := by
  obtain ⟨r,hr,htube⟩ := compact_negative_high_tube curve hQ hc hS hB hK hp hb he
  refine ⟨r,hr,?_⟩
  intro eta heta ε hε hεr
  have hh := htube eta heta (-(ε:ℂ)) (by simpa [abs_of_pos hε] using hεr)
  refine ⟨hh.1,hh.2.1,hh.2.2.2.2.mpr ?_⟩
  simpa only [Complex.mul_im,Complex.neg_re,Complex.ofReal_re,Complex.neg_im,Complex.ofReal_im,
    neg_zero,mul_zero,zero_add] using mul_pos_of_neg_of_neg hh.2.2.1 (neg_neg_of_pos hε)

end
end IsingBulk.Joint.Negative
