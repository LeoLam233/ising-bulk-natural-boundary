import IsingBulk.Final.LocalExtension

/-! Local-extension obstructions transfer by the two proved source symmetries. -/
namespace IsingBulk.Final
noncomputable section
open Filter Set
open scoped Topology

theorem no_extension_neg_of_even {f : ℂ → ℂ} {z : ℂ}
    (heven : ∀ s : ℂ, 1 < ‖s‖ → f (-s)=f s)
    (hz : ¬ HasExteriorExtension f z) : ¬ HasExteriorExtension f (-z) := by
  rintro ⟨U,hU,hzU,g,hg,heq⟩
  apply hz
  refine ⟨(fun s : ℂ => -s) ⁻¹' U,hU.preimage continuous_neg,by simpa using hzU,
    (fun s => g (-s)),?_,?_⟩
  · intro s hs
    exact (hg (-s) hs).comp analyticAt_id.neg
  · intro s hs
    dsimp only
    rw [heq ⟨hs.1,by simpa only [Set.mem_ofPred_eq,norm_neg] using hs.2⟩,heven s hs.2]

theorem analyticAt_conjugate_reflection {g : ℂ → ℂ} {s : ℂ}
    (hg : AnalyticAt ℂ g (star s)) : AnalyticAt ℂ (fun t => star (g (star t))) s := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [(continuous_star.tendsto s).eventually hg.eventually_analyticAt] with t ht
  simpa only [Function.comp_def,star_star] using ht.differentiableAt.star_star

theorem no_extension_conjugate_of_real_symmetry {f : ℂ → ℂ} {z : ℂ}
    (hreal : ∀ s : ℂ, 1 < ‖s‖ → f (star s)=star (f s))
    (hz : ¬ HasExteriorExtension f z) : ¬ HasExteriorExtension f (star z) := by
  rintro ⟨U,hU,hzU,g,hg,heq⟩
  apply hz
  refine ⟨star ⁻¹' U,hU.preimage continuous_star,hzU,
    (fun s => star (g (star s))),?_,?_⟩
  · intro s hs
    exact analyticAt_conjugate_reflection (hg (star s) hs)
  · intro s hs
    dsimp only
    rw [heq ⟨hs.1,by simpa only [Set.mem_ofPred_eq,norm_star] using hs.2⟩,hreal s hs.2,star_star]

end
end IsingBulk.Final
