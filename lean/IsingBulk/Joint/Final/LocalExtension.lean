import IsingBulk.Joint.Geometry.Definitions
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Topology.Connected.Clopen

namespace IsingBulk.Joint
noncomputable section
open Set Filter
open scoped Topology

section General
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Ordinary full-intersection holomorphic extension, not spectral continuation. -/
def HasFullExtension (D : Set E) (f : E → ℂ) (z : E) : Prop :=
  ∃ U : Set E, IsOpen U ∧ z ∈ U ∧ ∃ g : E → ℂ,
    AnalyticOnNhd ℂ g U ∧ EqOn g f (U ∩ D)

/-- Literal componentwise continuation in JOINT Definition 2.15. -/
def HasComponentExtension (D : Set E) (f : E → ℂ) (z : E) : Prop :=
  ∃ U : Set E, IsOpen U ∧ z ∈ U ∧ ∃ a ∈ D ∩ U,
    z ∈ closure (connectedComponentIn (D ∩ U) a) ∧ ∃ g : E → ℂ,
      AnalyticOnNhd ℂ g U ∧ EqOn g f (connectedComponentIn (D ∩ U) a)

/-- A purely topological local collar; it makes no assertion about a function. -/
def HasLocalCollar (D : Set E) : Prop :=
  ∀ z ∈ frontier D, ∀ U : Set E, IsOpen U → z ∈ U →
    ∀ a ∈ D ∩ U, z ∈ closure (connectedComponentIn (D ∩ U) a) →
      ∃ V : Set E, IsOpen V ∧ z ∈ V ∧ V ⊆ U ∧
        D ∩ V ⊆ connectedComponentIn (D ∩ U) a

theorem fullExtension_of_component {D : Set E} {f : E → ℂ}
    (hD : HasLocalCollar D) {z : E} (hz : z ∈ frontier D)
    (he : HasComponentExtension D f z) : HasFullExtension D f z := by
  obtain ⟨U,hU,hzU,a,ha,hza,g,hg,heq⟩ := he
  obtain ⟨V,hV,hzV,hVU,hVC⟩ := hD z hz U hU hzU a ha hza
  refine ⟨V,hV,hzV,g,hg.mono hVU,?_⟩
  intro w hw
  exact heq (hVC ⟨hw.2, hw.1⟩)

theorem no_fullExtension_on_closure {D G : Set E} {f : E → ℂ}
    (hG : ∀ z ∈ G, ¬ HasFullExtension D f z) {z : E} (hz : z ∈ closure G) :
    ¬ HasFullExtension D f z := by
  rintro ⟨U,hU,hzU,g,hg,he⟩
  obtain ⟨w,hwU,hwG⟩ := mem_closure_iff.mp hz U hU hzU
  exact hG w hwG ⟨U,hU,hwU,g,hg,he⟩

theorem no_componentExtension_of_dense {D G : Set E} {f : E → ℂ}
    (hD : HasLocalCollar D) (hd : frontier D ⊆ closure G)
    (hG : ∀ z ∈ G, ¬ HasFullExtension D f z) :
    ∀ z ∈ frontier D, ¬ HasComponentExtension D f z := by
  intro z hz he
  exact no_fullExtension_on_closure hG (hd hz) (fullExtension_of_component hD hz he)

/-- The valid direction: an actual transverse obstruction rules out ambient extension. -/
theorem fullExtension_pullback [CompleteSpace E] {D : Set E} {f : E → ℂ} {z : E}
    {c : ℂ → E} {t : ℂ} (hc : AnalyticAt ℂ c t) (hcz : c t = z)
    (he : HasFullExtension D f z) :
    HasFullExtension (c ⁻¹' D) (f ∘ c) t := by
  obtain ⟨U,hU,hzU,g,hg,heq⟩ := he
  let V : Set ℂ := {s | AnalyticAt ℂ c s}
  have hV : IsOpen V := isOpen_analyticAt ℂ c
  have htV : t ∈ V := hc
  have hcV : AnalyticOnNhd ℂ c V := fun _ hs => hs
  have hn : c ⁻¹' U ∈ 𝓝 t := hc.continuousAt.preimage_mem_nhds
    (hcz ▸ hU.mem_nhds hzU)
  obtain ⟨W,hWU,hW,htW⟩ := mem_nhds_iff.mp hn
  refine ⟨V ∩ W,hV.inter hW,⟨htV,htW⟩,g ∘ c,?_,?_⟩
  · intro s hs
    exact (hg (c s) (hWU hs.2)).comp (hcV s hs.1)
  · intro s hs
    exact heq ⟨hWU hs.1.2, hs.2⟩

end General
end
end IsingBulk.Joint
