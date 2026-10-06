import IsingBulk.First.ExteriorAnalyticGeometry
import Mathlib.Analysis.Analytic.IsolatedZeros

/-! Identity-theorem transfer from a real near-infinity germ to a named
holomorphic exterior continuation. No existence of that continuation, global
source-series convergence, or boundary-limit estimate is asserted. -/
namespace IsingBulk.First
noncomputable section
open Complex Set Filter
open scoped Topology

/-- A real half-line has an accumulation point inside the complex exterior,
so it identifies two genuine holomorphic exterior functions. -/
theorem exterior_eq_of_real_ray {R : ℝ} (hR : 0 ≤ R) {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (complexNormExterior R))
    (hg : AnalyticOnNhd ℂ g (complexNormExterior R))
    (hreal : ∀ x : ℝ, R < x → f (x:ℂ)=g (x:ℂ)) :
    EqOn f g (complexNormExterior R) := by
  let x₀ : ℝ := R+1
  have hx₀ : R < x₀ := by dsimp [x₀]; linarith
  have hx₀p : 0 < x₀ := hR.trans_lt hx₀
  have hxmem : (x₀:ℂ) ∈ complexNormExterior R := by
    change R < ‖(x₀:ℂ)‖
    rwa [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx₀p]
  have ht : Tendsto (fun x : ℝ => (x:ℂ)) (𝓝[>] x₀) (𝓝[≠] (x₀:ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds,?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    change (x:ℂ) ∉ ({(x₀:ℂ)} : Set ℂ)
    simp only [mem_singleton_iff,Complex.ofReal_inj]
    exact (lt_of_lt_of_le hx le_rfl).ne'
  have hfreq : ∃ᶠ x : ℝ in 𝓝[>] x₀, f (x:ℂ)=g (x:ℂ) := by
    apply Filter.Eventually.frequently
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hreal x (hx₀.trans hx)
  exact hf.eqOn_of_preconnected_of_frequently_eq hg (complexNormExterior_isPreconnected hR)
    hxmem (ht.frequently hfreq)

/-- Symmetry on any fixed far exterior propagates to a named holomorphic
continuation on the entire connected unit exterior. -/
theorem exterior_symmetry_of_near_infinity (chi : ℂ → ℂ)
    (hchi : AnalyticOnNhd ℂ chi (complexNormExterior 1))
    (heven : ∀ s : ℂ, 16 < ‖s‖ → chi (-s)=chi s)
    (hconj : ∀ s : ℂ, 16 < ‖s‖ → chi (star s)=star (chi s)) :
    ∀ s : ℂ, 1 < ‖s‖ → chi (-s)=chi s ∧ chi (star s)=star (chi s) := by
  have h17far : (17:ℂ) ∈ complexNormExterior 16 := by
    change 16 < ‖(17:ℂ)‖
    norm_num
  have h17near : (17:ℂ) ∈ complexNormExterior 1 := by
    change 1 < ‖(17:ℂ)‖
    norm_num
  have hdomain := (complexNormExterior_isOpen 16).mem_nhds h17far
  have hE : (fun s => chi (-s)) =ᶠ[𝓝 (17:ℂ)] chi := by
    filter_upwards [hdomain] with s hs
    exact heven s hs
  have hC : (fun s => star (chi (star s))) =ᶠ[𝓝 (17:ℂ)] chi := by
    filter_upwards [hdomain] with s hs
    rw [hconj s hs,star_star]
  have hEven := (analyticOnNhd_exterior_neg hchi).eqOn_of_preconnected_of_eventuallyEq hchi
    (complexNormExterior_isPreconnected (by norm_num : (0:ℝ) ≤ 1)) h17near hE
  have hConj := (analyticOnNhd_exterior_conjugate_reflection hchi).eqOn_of_preconnected_of_eventuallyEq hchi
    (complexNormExterior_isPreconnected (by norm_num : (0:ℝ) ≤ 1)) h17near hC
  intro s hs
  refine ⟨hEven hs,?_⟩
  simpa only [star_star] using congrArg star (hConj hs)

/-- The physical-facing continuation bridge. Its analytic-domain premise is
explicitly about the named function chi; F need be analytic only near infinity
and identified with chi only on the real near-infinity ray. -/
theorem exterior_symmetry_from_real_near_infinity (chi F : ℂ → ℂ)
    (hchi : AnalyticOnNhd ℂ chi (complexNormExterior 1))
    (hF : AnalyticOnNhd ℂ F (complexNormExterior 16))
    (hreal : ∀ x : ℝ, 16 < x → chi (x:ℂ)=F (x:ℂ))
    (hFeven : ∀ s : ℂ, 16 < ‖s‖ → F (-s)=F s)
    (hFconj : ∀ s : ℂ, 16 < ‖s‖ → F (star s)=star (F s)) :
    EqOn chi F (complexNormExterior 16) ∧
      ∀ s : ℂ, 1 < ‖s‖ → chi (-s)=chi s ∧ chi (star s)=star (chi s) := by
  have hc16 : AnalyticOnNhd ℂ chi (complexNormExterior 16) := by
    intro s hs
    apply hchi s
    change 16 < ‖s‖ at hs
    change 1 < ‖s‖
    linarith
  have hEq := exterior_eq_of_real_ray (by norm_num : (0:ℝ) ≤ 16) hc16 hF hreal
  refine ⟨hEq,exterior_symmetry_of_near_infinity chi hchi ?_ ?_⟩
  · intro s hs
    have hneg : chi (-s)=F (-s) := hEq (by simpa only [complexNormExterior,mem_ofPred_eq,norm_neg] using hs)
    have hhere : chi s=F s := hEq hs
    rw [hneg,hhere]
    exact hFeven s hs
  · intro s hs
    have hstar : chi (star s)=F (star s) := hEq (by simpa only [complexNormExterior,mem_ofPred_eq,norm_star] using hs)
    have hhere : chi s=F s := hEq hs
    rw [hstar,hhere]
    exact hFconj s hs

end
end IsingBulk.First
