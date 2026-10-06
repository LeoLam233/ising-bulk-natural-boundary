import IsingBulk.Final.LocalExtension

/-! Local nonzero analytic factors preserve the natural-boundary obstruction.
This is local: it does not assert single-valued inverse-temperature branches
on the whole exterior. -/
namespace IsingBulk.Final
noncomputable section
open Filter Set
open scoped Topology

theorem extension_of_analytic_factor_extension {f b : ℂ → ℂ} {z : ℂ}
    (hb : AnalyticAt ℂ b z) (hb0 : b z ≠ 0)
    (he : HasExteriorExtension (b*f) z) : HasExteriorExtension f z := by
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

theorem no_extension_mul_analytic_factor {f b : ℂ → ℂ} {z : ℂ}
    (hb : AnalyticAt ℂ b z) (hb0 : b z ≠ 0) (hf : ¬ HasExteriorExtension f z) :
    ¬ HasExteriorExtension (b*f) z :=
  fun he => hf (extension_of_analytic_factor_extension hb hb0 he)

end
end IsingBulk.Final
