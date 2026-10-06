import IsingBulk.First.ExteriorIdentitySymmetry

/-! A real near-infinity germ has at most one holomorphic continuation on the
whole unit exterior. This theorem does not assert that a continuation exists. -/
namespace IsingBulk.First
noncomputable section
open Complex Set Filter
open scoped Topology

theorem exterior_continuation_unique_from_real_near_infinity (f g : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (complexNormExterior 1))
    (hg : AnalyticOnNhd ℂ g (complexNormExterior 1))
    (hreal : ∀ x : ℝ, 16 < x → f (x:ℂ)=g (x:ℂ)) :
    EqOn f g (complexNormExterior 1) := by
  have hsub : complexNormExterior 16 ⊆ complexNormExterior 1 := by
    intro s hs
    change 16 < ‖s‖ at hs
    change 1 < ‖s‖
    linarith
  have hEq := exterior_eq_of_real_ray (by norm_num : (0:ℝ) ≤ 16)
    (hf.mono hsub) (hg.mono hsub) hreal
  have h17 : (17:ℂ) ∈ complexNormExterior 16 := by
    change 16 < ‖(17:ℂ)‖
    norm_num
  have he : f =ᶠ[𝓝 (17:ℂ)] g := by
    filter_upwards [(complexNormExterior_isOpen 16).mem_nhds h17] with s hs
    exact hEq hs
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg
    (complexNormExterior_isPreconnected (by norm_num : (0:ℝ) ≤ 1)) (hsub h17) he

end
end IsingBulk.First
