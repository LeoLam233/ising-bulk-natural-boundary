import IsingBulk.Joint.Transverse.NegativeEvenObstruction
import IsingBulk.Joint.Negative.FamilyChartIdentity

namespace IsingBulk.Joint.Transverse
noncomputable section
open Set Filter Metric RegularEdges
open IsingBulk.Anisotropic.RegularEdges
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

omit [NormedSpace ℂ E] in
/-- Local physical half-space charts at a compact family of centers give one
common tube. Membership in the actual physical domain is derived, not assumed. -/
theorem compact_family_negative_side_of_local {D : Set Coupling} {b : ℝ}
    (curve : ℂ × E→Coupling) {Q : Set E} (hQ : IsCompact Q)
    (hc : ∀eta∈Q,ContinuousAt curve (0,eta))
    (hlocal : ∀eta∈Q,∃U : Set Coupling,IsOpen U ∧ curve (0,eta)∈U ∧
      U⊆negativeFaceNeighborhood ∧ ∀L∈U,L∈D ↔ 0<(negativeParameter b L).im)
    {r : ℝ} (hr : 0<r)
    (hn : ∀eta∈Q,∀u : ℂ,‖u‖<r → negativeParameter b (curve (u,eta))=u) :
    ∃δ : ℝ,0<δ ∧ ∀eta∈Q,∀u : ℂ,‖u‖<δ →
      curve (u,eta)∈negativeFaceNeighborhood ∧
      negativeParameter b (curve (u,eta))=u ∧ (curve (u,eta)∈D ↔ 0<u.im) := by
  let V : Set Coupling := {K | ∃U : Set Coupling,IsOpen U ∧ K∈U ∧
    U⊆negativeFaceNeighborhood ∧ ∀L∈U,L∈D ↔ 0<(negativeParameter b L).im}
  have hV : IsOpen V := by
    rw [isOpen_iff_mem_nhds]
    rintro K ⟨U,hU,hKU,hUf,hside⟩
    exact Filter.mem_of_superset (hU.mem_nhds hKU) (fun L hL=>⟨U,hU,hL,hUf,hside⟩)
  have hev : ∀ᶠu in 𝓝 (0:ℂ),∀eta∈Q,curve (u,eta)∈V := by
    apply hQ.eventually_forall_of_forall_eventually
    intro eta heta
    exact (hc eta heta).preimage_mem_nhds (hV.mem_nhds (hlocal eta heta))
  obtain ⟨a,ha,hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨min a r,lt_min ha hr,?_⟩
  intro eta heta u hu
  obtain ⟨U,_hU,hcU,hUf,hside⟩ := hball (by simpa using hu.trans_le (min_le_left _ _)) eta heta
  have he := hn eta heta u (hu.trans_le (min_le_right _ _))
  exact ⟨hUf hcU,he,by simpa only [he] using hside _ hcU⟩

theorem compact_family_negative_low_side {b : ℝ} (curve : ℂ × E→Coupling)
    {Q : Set E} (hQ : IsCompact Q) (hc : ∀eta∈Q,AnalyticAt ℂ curve (0,eta))
    (hK : ∀eta∈Q,curve (0,eta)∈frontier lowDomain)
    (hS : ∀eta∈Q,S (curve (0,eta))≠0) (hp : ∀eta∈Q,p (curve (0,eta))^2≠1)
    (hB : ∀eta∈Q,0<(-transferB (curve (0,eta))).im) (hb : |b|<1)
    {r : ℝ} (hr : 0<r)
    (hn : ∀eta∈Q,∀u : ℂ,‖u‖<r → negativeParameter b (curve (u,eta))=u) :
    ∃δ : ℝ,0<δ ∧ ∀eta∈Q,∀u : ℂ,‖u‖<δ →
      curve (u,eta)∈negativeFaceNeighborhood ∧
      negativeParameter b (curve (u,eta))=u ∧ (curve (u,eta)∈lowDomain ↔ 0<u.im) := by
  apply compact_family_negative_side_of_local curve hQ (fun eta heta=>(hc eta heta).continuousAt) _ hr hn
  intro eta heta
  exact negativeFace_low_side (hK eta heta) (hS eta heta) (hp eta heta) (hB eta heta) hb
    (hn eta heta 0 (by simpa using hr))

theorem compact_family_negative_low_tube {b : ℝ} (curve : ℂ × E→Coupling)
    {Q : Set E} (hQ : IsCompact Q) (hc : ∀eta∈Q,AnalyticAt ℂ curve (0,eta))
    (hK : ∀eta∈Q,curve (0,eta)∈frontier lowDomain)
    (hS : ∀eta∈Q,S (curve (0,eta))≠0) (hp : ∀eta∈Q,p (curve (0,eta))^2≠1)
    (hB : ∀eta∈Q,0<(-transferB (curve (0,eta))).im) (hb : |b|<1)
    (hn : ∀eta∈Q,∀ᶠu : ℂ in 𝓝 0,negativeParameter b (curve (u,eta))=u) :
    ∃δ : ℝ,0<δ ∧ ∀eta∈Q,∀u : ℂ,‖u‖<δ →
      AnalyticAt ℂ curve (u,eta) ∧ S (curve (u,eta))≠0 ∧
      0<(-transferB (curve (u,eta))).im ∧ negativeParameter b (curve (u,eta))=u ∧
      (curve (u,eta)∈lowDomain ↔ 0<u.im) := by
  obtain ⟨r,hr,hnorm⟩ := Negative.compact_family_analytic_identity
    (fun q => negativeParameter b (curve q)) (fun q : ℂ × E => q.1) hQ
    (fun eta heta => (((transferC_analyticAt (hS eta heta)).comp (hc eta heta)).add
      ((transferB_analyticAt (hS eta heta)).comp (hc eta heta))).sub analyticAt_const)
    (fun _ _ => analyticAt_fst) hn
  obtain ⟨a,ha,hside⟩ := compact_family_negative_low_side curve hQ hc hK hS hp hB hb hr hnorm
  obtain ⟨d,M,hd,_hM,hcurve⟩ := Negative.compact_analytic_uniform_bound curve hQ hc
  refine ⟨min a d,lt_min ha hd,?_⟩
  intro eta heta u hu
  obtain ⟨hface,he,hdom⟩ := hside eta heta u (hu.trans_le (min_le_left _ _))
  exact ⟨(hcurve eta heta u (hu.trans_le (min_le_right _ _))).1,hface.1,hface.2.1,he,hdom⟩

end
end IsingBulk.Joint.Transverse
