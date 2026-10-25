import IsingBulk.Joint.Final.LocalExtension
import Mathlib.Analysis.Complex.CauchyIntegral

namespace IsingBulk.Joint
noncomputable section
open Set Filter
open scoped Topology

section General
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Ordinary complex Fréchet-holomorphic extension; no power-series premise is
imposed on a purported multivariable extension. -/
def HasHolomorphicFullExtension (D : Set E) (f : E → ℂ) (z : E) : Prop :=
  ∃ U : Set E, IsOpen U ∧ z ∈ U ∧ ∃ g : E → ℂ,
    DifferentiableOn ℂ g U ∧ EqOn g f (U ∩ D)

def HasHolomorphicComponentExtension (D : Set E) (f : E → ℂ) (z : E) : Prop :=
  ∃ U : Set E, IsOpen U ∧ z ∈ U ∧ ∃ a ∈ D ∩ U,
    z ∈ closure (connectedComponentIn (D ∩ U) a) ∧ ∃ g : E → ℂ,
      DifferentiableOn ℂ g U ∧ EqOn g f (connectedComponentIn (D ∩ U) a)

theorem holomorphicFullExtension_of_component {D : Set E} {f : E → ℂ}
    (hD : HasLocalCollar D) {z : E} (hz : z ∈ frontier D)
    (he : HasHolomorphicComponentExtension D f z) : HasHolomorphicFullExtension D f z := by
  obtain ⟨U,hU,hzU,a,ha,hza,g,hg,heq⟩ := he
  obtain ⟨V,hV,hzV,hVU,hVC⟩ := hD z hz U hU hzU a ha hza
  refine ⟨V,hV,hzV,g,hg.mono hVU,?_⟩
  intro w hw
  exact heq (hVC ⟨hw.2,hw.1⟩)

theorem no_holomorphicFullExtension_on_closure {D G : Set E} {f : E → ℂ}
    (hG : ∀ z ∈ G, ¬ HasHolomorphicFullExtension D f z) {z : E} (hz : z ∈ closure G) :
    ¬ HasHolomorphicFullExtension D f z := by
  rintro ⟨U,hU,hzU,g,hg,he⟩
  obtain ⟨w,hwU,hwG⟩ := mem_closure_iff.mp hz U hU hzU
  exact hG w hwG ⟨U,hU,hwU,g,hg,he⟩

theorem no_holomorphicComponentExtension_of_dense {D G : Set E} {f : E → ℂ}
    (hD : HasLocalCollar D) (hd : frontier D ⊆ closure G)
    (hG : ∀ z ∈ G, ¬ HasHolomorphicFullExtension D f z) :
    ∀ z ∈ frontier D, ¬ HasHolomorphicComponentExtension D f z := by
  intro z hz he
  exact no_holomorphicFullExtension_on_closure hG (hd hz)
    (holomorphicFullExtension_of_component hD hz he)

theorem analytic_scalar_pullback_of_holomorphic_extension [CompleteSpace E]
    {D : Set E} {f : E → ℂ} {z : E} {c : ℂ → E} {t : ℂ}
    (hc : AnalyticAt ℂ c t) (hcz : c t = z)
    (he : HasHolomorphicFullExtension D f z) :
    HasFullExtension (c ⁻¹' D) (f ∘ c) t := by
  obtain ⟨U,hU,hzU,g,hg,heq⟩ := he
  let V : Set ℂ := {s | AnalyticAt ℂ c s}
  have hV : IsOpen V := isOpen_analyticAt ℂ c
  have htV : t ∈ V := hc
  have hn : c ⁻¹' U ∈ 𝓝 t := hc.continuousAt.preimage_mem_nhds
    (hcz ▸ hU.mem_nhds hzU)
  obtain ⟨W,hWU,hW,htW⟩ := mem_nhds_iff.mp hn
  refine ⟨V ∩ W,hV.inter hW,⟨htV,htW⟩,g ∘ c,?_,?_⟩
  · apply DifferentiableOn.analyticOnNhd _ (hV.inter hW)
    intro s hs
    exact ((hg (c s) (hWU hs.2)).differentiableAt (hU.mem_nhds (hWU hs.2))).comp s
      (show AnalyticAt ℂ c s from hs.1).differentiableAt |>.differentiableWithinAt
  · intro s hs
    exact heq ⟨hWU hs.1.2,hs.2⟩

/-- Ordinary holomorphic natural boundary in the componentwise sense. -/
def HolomorphicNaturalBoundaryOn (D : Set E) (f : E → ℂ) : Prop :=
  DifferentiableOn ℂ f D ∧ ∀ z ∈ frontier D, ¬ HasHolomorphicComponentExtension D f z

end General
theorem scalar_fullExtension_of_holomorphic {D : Set ℂ} {f : ℂ → ℂ} {z : ℂ}
    (he : HasHolomorphicFullExtension D f z) : HasFullExtension D f z := by
  obtain ⟨U,hU,hzU,g,hg,heq⟩ := he
  exact ⟨U,hU,hzU,g,hg.analyticOnNhd hU,heq⟩

end
end IsingBulk.Joint
