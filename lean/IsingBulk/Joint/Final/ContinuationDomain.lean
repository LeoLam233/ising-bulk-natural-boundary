import IsingBulk.Joint.Final.ContinuationIdentity
import Mathlib.Topology.Path

namespace IsingBulk.Joint
noncomputable section
open Set Filter Metric
open scoped Topology

/-- An unramified Riemann domain over C² carrying a holomorphic section.
The charts are actual local homeomorphisms of the projection; their transition
maps are the identity on overlapping base sheets. No physical domain or function
is mentioned in this definition. -/
structure UnramifiedHolomorphicDomain (M : Type*) [TopologicalSpace M] where
  projection : M → Coupling
  value : M → ℂ
  chart : M → OpenPartialHomeomorph M Coupling
  mem_source : ∀ m, m ∈ (chart m).source
  chart_eq : ∀ m, (chart m : M → Coupling) = projection
  holomorphic : ∀ m, DifferentiableOn ℂ (value ∘ (chart m).symm) (chart m).target

namespace UnramifiedHolomorphicDomain
variable {M : Type*} [TopologicalSpace M] (R : UnramifiedHolomorphicDomain M)

@[fun_prop] theorem continuous_projection : Continuous R.projection := by
  apply continuous_iff_continuousAt.mpr
  intro m
  rw [←R.chart_eq m]
  exact (R.chart m).continuousAt (R.mem_source m)

/-- Ordinary equality of local germs upstairs. -/
def GermAgreement (f : Coupling → ℂ) : Set M :=
  interior {m | R.value m = f (R.projection m)}

theorem germAgreement_iff {f : Coupling → ℂ} {m : M} :
    m ∈ R.GermAgreement f ↔ R.value =ᶠ[𝓝 m] f ∘ R.projection :=
  mem_interior_iff_mem_nhds

theorem germAgreement_chart {f : Coupling → ℂ} {m : M}
    (hm : m ∈ R.GermAgreement f) (e : OpenPartialHomeomorph M Coupling)
    (he : (e : M → Coupling) = R.projection) (hms : m ∈ e.source) :
    R.value ∘ e.symm =ᶠ[𝓝 (R.projection m)] f := by
  have hh := (e.tendsto_symm hms).eventually (R.germAgreement_iff.mp hm)
  rw [he] at hh
  have ht : e.target ∈ 𝓝 (R.projection m) := by rw [←he]; exact e.open_target.mem_nhds (e.map_source hms)
  filter_upwards [hh,ht] with z hz hzt
  change R.value (e.symm z) = f z
  rw [hz]
  change f (R.projection (e.symm z)) = f z
  rw [←he,e.right_inv hzt]

/-- Holomorphic uniqueness proves relative closedness of physical-germ agreement
inside the physical domain. This is not assumed as continuation data. -/
theorem closure_germAgreement_inter_subset {D : Set Coupling} (hD : IsOpen D)
    {f : Coupling → ℂ} (hf : DifferentiableOn ℂ f D) :
    closure (R.GermAgreement f) ∩ R.projection ⁻¹' D ⊆ R.GermAgreement f := by
  rintro m ⟨hm,hmD⟩
  let e := R.chart m
  have hms : m ∈ e.source := R.mem_source m
  have he : (e : M → Coupling) = R.projection := R.chart_eq m
  have hmt : R.projection m ∈ e.target := by rw [←he]; exact e.map_source hms
  obtain ⟨r,hr,hrsub⟩ := Metric.isOpen_iff.mp (e.open_target.inter hD)
    (R.projection m) ⟨hmt,hmD⟩
  let W : Set M := e.source ∩ e ⁻¹' ball (R.projection m) r
  have hW : IsOpen W := e.isOpen_inter_preimage isOpen_ball
  have hmW : m ∈ W := ⟨hms,by rw [he]; exact mem_ball_self hr⟩
  obtain ⟨n,hnW,hnG⟩ := mem_closure_iff.mp hm W hW hmW
  have hnf : R.value ∘ e.symm =ᶠ[𝓝 (e n)] f := by
    rw [he]
    exact R.germAgreement_chart hnG e he hnW.1
  have hfg : EqOn (R.value ∘ e.symm) f (ball (R.projection m) r) :=
    holomorphic_eqOn_convex isOpen_ball (convex_ball _ _)
      ((R.holomorphic m).mono (fun _ h => (hrsub h).1))
      (hf.mono (fun _ h => (hrsub h).2)) hnW.2 hnf
  apply R.germAgreement_iff.mpr
  have hnb : ∀ᶠ n in 𝓝 m, n ∈ W := hW.mem_nhds hmW
  filter_upwards [hnb] with n hn
  have hh := hfg hn.2
  change R.value (e.symm (e n)) = f (e n) at hh
  rw [e.left_inv hn.1] at hh
  simpa only [he,Function.comp_apply] using hh

/-- Agreement follows on any connected lifted region over D from just one
initial physical germ. -/
theorem agreement_on_preconnected {D : Set Coupling} (hD : IsOpen D)
    {f : Coupling → ℂ} (hf : DifferentiableOn ℂ f D) {C : Set M}
    (hC : IsPreconnected C) (hCD : C ⊆ R.projection ⁻¹' D)
    {m : M} (hmC : m ∈ C) (hm : m ∈ R.GermAgreement f) : C ⊆ R.GermAgreement f := by
  apply hC.subset_of_closure_inter_subset isOpen_interior ⟨m,hmC,hm⟩
  intro n hn
  exact R.closure_germAgreement_inter_subset hD hf ⟨hn.1,hCD hn.2⟩

end UnramifiedHolomorphicDomain
end
end IsingBulk.Joint
