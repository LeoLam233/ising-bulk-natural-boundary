import IsingBulk.Joint.Final.ContinuationDomain
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Connected.LocallyConnected

namespace IsingBulk.Joint
noncomputable section
open Set Filter Metric
open scoped Topology

/-- Compactness of the finite parameter interval produces an actual first exit. -/
theorem finite_first_exit {D : Set Coupling} (hD : IsOpen D) {γ : ℝ → Coupling}
    (hγ : Continuous γ) (h0 : γ 0 ∈ D)
    (hout : ∃ t ∈ Icc (0 : ℝ) 1, γ t ∉ D) :
    ∃ τ ∈ Ioc (0 : ℝ) 1, γ τ ∈ frontier D ∧ ∀ t ∈ Ico (0 : ℝ) τ, γ t ∈ D := by
  let E : Set ℝ := Icc 0 1 ∩ γ ⁻¹' Dᶜ
  have hE : IsCompact E := isCompact_Icc.inter_right (hD.isClosed_compl.preimage hγ)
  have hEne : E.Nonempty := by obtain ⟨t,ht,ho⟩ := hout; exact ⟨t,ht,ho⟩
  obtain ⟨τ,hτ,hmin⟩ := hE.exists_isLeast hEne
  have hτpos : 0 < τ := by
    by_contra hn
    have he : τ = 0 := le_antisymm (le_of_not_gt hn) hτ.1.1
    exact hτ.2 (he ▸ h0)
  have hbefore : ∀ t ∈ Ico (0 : ℝ) τ, γ t ∈ D := by
    intro t ht
    by_contra hn
    have hh := hmin (show t ∈ E from ⟨⟨ht.1,ht.2.le.trans hτ.1.2⟩,hn⟩)
    exact (not_le_of_gt ht.2) hh
  have hcl : τ ∈ closure (Ico (0 : ℝ) τ) := by rw [closure_Ico hτpos.ne]; exact ⟨hτpos.le,le_rfl⟩
  have hb : γ τ ∈ closure D := (show MapsTo γ (Ico 0 τ) D from hbefore).closure hγ hcl
  refine ⟨τ,⟨hτpos,hτ.1.2⟩,?_,hbefore⟩
  rw [hD.frontier_eq]
  exact ⟨hb,hτ.2⟩

namespace UnramifiedHolomorphicDomain
variable {M : Type*} [TopologicalSpace M] (R : UnramifiedHolomorphicDomain M)

/-- A reached unramified chart at a first exit yields an ordinary holomorphic
component extension. Germ agreement before exit is proved from the initial germ. -/
theorem first_exit_component_extension {D : Set Coupling} (hD : IsOpen D)
    {f : Coupling → ℂ} (hf : DifferentiableOn ℂ f D) {γ : ℝ → M}
    (hγ : Continuous γ) (hstart : γ 0 ∈ R.GermAgreement f)
    {τ : ℝ} (hτ : 0 < τ) (hbefore : ∀ t ∈ Ico (0 : ℝ) τ, R.projection (γ t) ∈ D) :
    HasHolomorphicComponentExtension D f (R.projection (γ τ)) := by
  have hproj : Continuous (R.projection ∘ γ) := R.continuous_projection.comp hγ
  have hagree : ∀ t ∈ Ico (0 : ℝ) τ, γ t ∈ R.GermAgreement f := by
    have hc : IsPreconnected (γ '' Ico (0 : ℝ) τ) := isPreconnected_Ico.image γ hγ.continuousOn
    have hCD : γ '' Ico (0 : ℝ) τ ⊆ R.projection ⁻¹' D := by
      rintro m ⟨t,ht,rfl⟩
      exact hbefore t ht
    have hh := R.agreement_on_preconnected hD hf hc hCD
      (mem_image_of_mem γ (show (0 : ℝ) ∈ Ico 0 τ from ⟨le_rfl,hτ⟩)) hstart
    exact fun t ht => hh (mem_image_of_mem γ ht)
  let e := R.chart (γ τ)
  have he : (e : M → Coupling) = R.projection := R.chart_eq _
  have hms : γ τ ∈ e.source := R.mem_source _
  have hnt : γ ⁻¹' e.source ∈ 𝓝 τ := hγ.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds hms)
  obtain ⟨δ,hδ,hδs⟩ := Metric.mem_nhds_iff.mp hnt
  obtain ⟨a,ha,haτ⟩ := exists_between (show max 0 (τ-δ) < τ by rw [max_lt_iff]; exact ⟨hτ,by linarith⟩)
  have ha0 : 0 ≤ a := (le_max_left _ _).trans ha.le
  have had : τ-δ < a := (le_max_right _ _).trans_lt ha
  have hs : ∀ t ∈ Ico a τ, γ t ∈ e.source := by
    intro t ht
    apply hδs
    rw [mem_ball,Real.dist_eq,abs_of_neg (by linarith [ht.2] : t-τ < 0)]
    linarith [ht.1]
  have hside : MapsTo (R.projection ∘ γ) (Ico a τ) (D ∩ e.target) := by
    intro t ht
    refine ⟨hbefore t ⟨ha0.trans ht.1,ht.2⟩,?_⟩
    rw [←he]
    exact e.map_source (hs t ht)
  have haI : a ∈ Ico a τ := ⟨le_rfl,haτ⟩
  have haDU : R.projection (γ a) ∈ D ∩ e.target := hside haI
  let C := connectedComponentIn (D ∩ e.target) (R.projection (γ a))
  have himage : (R.projection ∘ γ) '' Ico a τ ⊆ C :=
    (isPreconnected_Ico.image _ hproj.continuousOn).subset_connectedComponentIn
      (mem_image_of_mem _ haI) (by rintro z ⟨t,ht,rfl⟩; exact hside ht)
  have hcl : R.projection (γ τ) ∈ closure C := by
    have htcl : τ ∈ closure (Ico a τ) := by rw [closure_Ico haτ.ne]; exact ⟨haτ.le,le_rfl⟩
    exact closure_mono himage ((show MapsTo (R.projection ∘ γ) (Ico a τ)
      ((R.projection ∘ γ) '' Ico a τ) from fun t ht => mem_image_of_mem _ ht).closure hproj htcl)
  have hCopen : IsOpen C := (hD.inter e.open_target).connectedComponentIn
  have hCsub : C ⊆ D ∩ e.target := connectedComponentIn_subset _ _
  have haC : R.projection (γ a) ∈ C := mem_connectedComponentIn haDU
  have hgf := R.germAgreement_chart (hagree a ⟨ha0,haτ⟩) e he (hs a haI)
  have hEq : EqOn (R.value ∘ e.symm) f C := holomorphic_eqOn_preconnected hCopen
    isPreconnected_connectedComponentIn ((R.holomorphic _).mono (fun _ h => (hCsub h).2))
    (hf.mono (fun _ h => (hCsub h).1)) haC hgf
  refine ⟨e.target,e.open_target,?_,R.projection (γ a),haDU,hcl,
    R.value ∘ e.symm,R.holomorphic _,hEq⟩
  rw [←he]
  exact e.map_source hms

/-- A finite lifted continuation path from the physical germ cannot leave D. -/
theorem path_stays_in_domain {D : Set Coupling} (hD : IsOpen D) {f : Coupling → ℂ}
    (hnb : HolomorphicNaturalBoundaryOn D f) {γ : ℝ → M} (hγ : Continuous γ)
    (h0 : R.projection (γ 0) ∈ D) (hstart : γ 0 ∈ R.GermAgreement f) :
    ∀ t ∈ Icc (0 : ℝ) 1, R.projection (γ t) ∈ D := by
  by_contra hn
  push Not at hn
  obtain ⟨τ,hτ,hboundary,hbefore⟩ := finite_first_exit hD (R.continuous_projection.comp hγ) h0 hn
  exact hnb.2 _ hboundary (R.first_exit_component_extension hD hnb.1 hγ hstart hτ.1 hbefore)

/-- Standard compact-interval paths, with no chosen global parameter extension. -/
theorem finite_path_stays_in_domain {D : Set Coupling} (hD : IsOpen D) {f : Coupling → ℂ}
    (hnb : HolomorphicNaturalBoundaryOn D f) {m n : M} (γ : Path m n)
    (hm : R.projection m ∈ D) (hstart : m ∈ R.GermAgreement f) :
    ∀ t : unitInterval, R.projection (γ t) ∈ D := by
  have hh := R.path_stays_in_domain hD hnb γ.continuous_extend
    (by simpa only [γ.extend_zero] using hm) (by simpa only [γ.extend_zero] using hstart)
  intro t
  simpa only [γ.extend_extends' t] using hh t t.property

end UnramifiedHolomorphicDomain
end
end IsingBulk.Joint
