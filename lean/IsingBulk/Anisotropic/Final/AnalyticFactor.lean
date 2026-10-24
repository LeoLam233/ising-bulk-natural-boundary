import IsingBulk.Anisotropic.Final.LocalExtension
import Mathlib.Analysis.Analytic.Constructions

namespace IsingBulk.Anisotropic
noncomputable section
open Filter Set
open scoped Topology

theorem domain_extension_of_analytic_factor {D : Set ℂ} {f b : ℂ → ℂ} {z : ℂ}
    (hb : AnalyticAt ℂ b z) (hb0 : b z ≠ 0)
    (he : HasDomainExtension D (b*f) z) : HasDomainExtension D f z := by
  obtain ⟨U,hU,hzU,g,hg,hgf⟩ := he
  have hlocal : ∀ᶠ s in 𝓝 z, AnalyticAt ℂ b s ∧ b s ≠ 0 :=
    hb.eventually_analyticAt.and (hb.continuousAt.eventually_ne hb0)
  obtain ⟨V,hV,hVopen,hzV⟩ := mem_nhds_iff.mp hlocal
  refine ⟨U ∩ V,hU.inter hVopen,⟨hzU,hzV⟩,(fun s => g s / b s),?_,?_⟩
  · intro s hs
    exact (hg s hs.1).div (hV hs.2).1 (hV hs.2).2
  · intro s hs
    dsimp only
    rw [hgf ⟨hs.1.1,hs.2⟩]
    simp only [Pi.mul_apply]
    exact mul_div_cancel_left₀ (f s) (hV hs.1.2).2

theorem no_domain_extension_mul_analytic_factor {D : Set ℂ} {f b : ℂ → ℂ} {z : ℂ}
    (hb : AnalyticAt ℂ b z) (hb0 : b z ≠ 0) (hf : ¬ HasDomainExtension D f z) :
    ¬ HasDomainExtension D (b*f) z :=
  fun he => hf (domain_extension_of_analytic_factor hb hb0 he)

/-- Actual energy-field factor in the z coordinate. -/
def inverseTemperature (J : ℝ) (z : ℂ) : ℂ := z / (2 * (J : ℂ))

theorem inverseTemperature_analytic (J : ℝ) (z : ℂ) :
    AnalyticAt ℂ (inverseTemperature J) z := by
  exact analyticAt_id.div_const

theorem inverseTemperature_ne_zero {J : ℝ} (hJ : 0 < J) {z : ℂ} (hz : z ≠ 0) :
    inverseTemperature J z ≠ 0 := by
  exact div_ne_zero hz (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr (ne_of_gt hJ)))

theorem physical_response_no_extension {J : ℝ} (hJ : 0 < J) {D : Set ℂ}
    {X : ℂ → ℂ} {z : ℂ} (hz : z ≠ 0) (hX : ¬ HasDomainExtension D X z) :
    ¬ HasDomainExtension D (inverseTemperature J * X) z :=
  no_domain_extension_mul_analytic_factor (inverseTemperature_analytic J z)
    (inverseTemperature_ne_zero hJ hz) hX

end
end IsingBulk.Anisotropic
