import IsingBulk.Anisotropic.Final.LocalExtension
import IsingBulk.Anisotropic.Final.AnalyticInverse
import Mathlib.Analysis.Analytic.Composition

namespace IsingBulk.Anisotropic
noncomputable section
open Set Filter
open scoped Topology

/-- A genuine local analytic inverse transports an extension of an actual
pullback back to the target domain. Domain-side inclusion is explicit. -/
theorem domain_extension_of_local_pullback {D E V : Set ℂ} {f φ ψ : ℂ → ℂ}
    {z : ℂ} (hV : IsOpen V) (hzV : φ z ∈ V)
    (hψ : AnalyticOnNhd ℂ ψ V) (hleft : ψ (φ z) = z)
    (hright : ∀ w ∈ V, φ (ψ w) = w)
    (hside : ∀ w ∈ V ∩ E, ψ w ∈ D)
    (he : HasDomainExtension D (f ∘ φ) z) : HasDomainExtension E f (φ z) := by
  obtain ⟨U,hU,hzU,g,hg,hEq⟩ := he
  let W : Set ℂ := V ∩ ψ ⁻¹' U
  have hW : IsOpen W := by
    apply isOpen_iff_mem_nhds.mpr
    intro w hw
    exact inter_mem (hV.mem_nhds hw.1)
      ((hψ w hw.1).continuousAt.eventually (hU.mem_nhds hw.2))
  refine ⟨W,hW,⟨hzV,by simpa [hleft] using hzU⟩,g ∘ ψ,?_,?_⟩
  · intro w hw
    exact (hg (ψ w) hw.2).comp (hψ w hw.1)
  · intro w hw
    have h := hEq ⟨hw.1.2,hside w ⟨hw.1.1,hw.2⟩⟩
    simpa only [Function.comp_apply,hright w hw.1.1] using h

theorem no_domain_extension_pullback {D E V : Set ℂ} {f φ ψ : ℂ → ℂ}
    {z : ℂ} (hV : IsOpen V) (hzV : φ z ∈ V)
    (hψ : AnalyticOnNhd ℂ ψ V) (hleft : ψ (φ z) = z)
    (hright : ∀ w ∈ V, φ (ψ w) = w)
    (hside : ∀ w ∈ V ∩ E, ψ w ∈ D)
    (hf : ¬ HasDomainExtension E f (φ z)) :
    ¬ HasDomainExtension D (f ∘ φ) z :=
  fun he => hf (domain_extension_of_local_pullback hV hzV hψ hleft hright hside he)

/-- The inverse is derived from a nonzero analytic derivative. The only domain
condition is a genuine local inclusion, not an extension assertion. -/
theorem no_domain_extension_analytic_pullback {D E : Set ℂ} {f φ : ℂ → ℂ}
    {z : ℂ} (hφ : AnalyticAt ℂ φ z) (hd : deriv φ z ≠ 0)
    (hside : ∀ᶠ v in 𝓝 z, φ v ∈ E → v ∈ D)
    (hf : ¬ HasDomainExtension E f (φ z)) :
    ¬ HasDomainExtension D (f ∘ φ) z := by
  obtain ⟨ψ,ha,hl,hr,_⟩ := exists_analytic_local_inverse hφ hd
  have hnear : ∀ᶠ w in 𝓝 (φ z), φ (ψ w) ∈ E → ψ w ∈ D := by
    have hc : Tendsto ψ (𝓝 (φ z)) (𝓝 z) := by
      simpa only [hl] using ha.continuousAt.tendsto
    exact hc.eventually hside
  have hv : ∀ᶠ w in 𝓝 (φ z),
      AnalyticAt ℂ ψ w ∧ φ (ψ w) = w ∧ (w ∈ E → ψ w ∈ D) := by
    filter_upwards [ha.eventually_analyticAt,hr,hnear] with w haw hrw hnw
    exact ⟨haw,hrw,fun hw => hnw (by simpa only [hrw] using hw)⟩
  obtain ⟨V,hV,hVo,hzV⟩ := mem_nhds_iff.mp hv
  exact no_domain_extension_pullback hVo hzV (fun w hw => (hV hw).1) hl
    (fun w hw => (hV hw).2.1) (fun w hw => (hV hw.1).2.2 hw.2) hf

/-- In particular, analytic pullback to the literal preimage preserves every
noncritical boundary obstruction. -/
theorem no_domain_extension_preimage {E : Set ℂ} {f φ : ℂ → ℂ} {z : ℂ}
    (hφ : AnalyticAt ℂ φ z) (hd : deriv φ z ≠ 0)
    (hf : ¬ HasDomainExtension E f (φ z)) :
    ¬ HasDomainExtension (φ ⁻¹' E) (f ∘ φ) z :=
  no_domain_extension_analytic_pullback hφ hd
    (Eventually.of_forall fun _ h => h) hf

end
end IsingBulk.Anisotropic
