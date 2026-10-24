import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Topology.MetricSpace.Basic

/-! Genuine local extensions on an independently specified domain. The lemmas
are general transport/closure facts; no ANISO singularity is an assumption of
an ANISO endpoint here. -/
namespace IsingBulk.Anisotropic
noncomputable section
open Set Filter
open scoped Topology

def HasDomainExtension (D : Set ℂ) (f : ℂ → ℂ) (z : ℂ) : Prop :=
  ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧ ∃ g : ℂ → ℂ,
    AnalyticOnNhd ℂ g U ∧ EqOn g f (U ∩ D)

def NaturalBoundaryOn (D : Set ℂ) (f : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ f D ∧ ∀ z ∈ frontier D, ¬ HasDomainExtension D f z

theorem no_domain_extension_on_closure {D S : Set ℂ} {f : ℂ → ℂ}
    (hS : ∀ z ∈ S, ¬ HasDomainExtension D f z) {z : ℂ} (hz : z ∈ closure S) :
    ¬ HasDomainExtension D f z := by
  rintro ⟨U,hU,hzU,g,hg,heq⟩
  obtain ⟨w,hwU,hwS⟩ := mem_closure_iff.mp hz U hU hzU
  exact hS w hwS ⟨U,hU,hwU,g,hg,heq⟩

theorem naturalBoundaryOn_of_dense_obstructions {D S : Set ℂ} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f D) (hd : frontier D ⊆ closure S)
    (hS : ∀ z ∈ S, ¬ HasDomainExtension D f z) : NaturalBoundaryOn D f :=
  ⟨hf, fun _ hz => no_domain_extension_on_closure hS (hd hz)⟩

theorem domain_extension_of_eventuallyEq {D : Set ℂ} {f g : ℂ → ℂ} {z : ℂ}
    (hfg : ∀ᶠ s in 𝓝 z, s ∈ D → f s = g s)
    (hg : HasDomainExtension D g z) : HasDomainExtension D f z := by
  obtain ⟨U,hU,hzU,G,hG,hEq⟩ := hg
  obtain ⟨V,hV,hVopen,hzV⟩ := mem_nhds_iff.mp hfg
  refine ⟨U ∩ V,hU.inter hVopen,⟨hzU,hzV⟩,G,hG.mono inter_subset_left,?_⟩
  intro s hs
  exact (hEq ⟨hs.1.1,hs.2⟩).trans (hV hs.1.2 hs.2).symm

theorem domain_extension_of_eqOn {D : Set ℂ} {f g : ℂ → ℂ} {z : ℂ}
    (hfg : EqOn f g D) (hg : HasDomainExtension D g z) : HasDomainExtension D f z :=
  domain_extension_of_eventuallyEq (Eventually.of_forall fun _ hs => hfg hs) hg

theorem no_domain_extension_of_eqOn {D : Set ℂ} {f g : ℂ → ℂ} {z : ℂ}
    (hfg : EqOn f g D) (hf : ¬ HasDomainExtension D f z) :
    ¬ HasDomainExtension D g z := fun hg => hf (domain_extension_of_eqOn hfg hg)

end
end IsingBulk.Anisotropic
