import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic

/-! Analytic uniqueness from a real interval, isolated from the physical
representation and boundary theorem. The interval has an explicit interior
accumulation point, and the whole complex unit disk is connected. -/
namespace IsingBulk.HT.Final
noncomputable section
open Set Filter
open scoped Topology

/-- Equality on the prescribed real high-temperature germ determines two
analytic functions on the whole connected unit disk, including the origin. -/
theorem analytic_unitDisk_eq_of_real_germ {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f {s : ℂ | ‖s‖ < 1})
    (hg : AnalyticOnNhd ℂ g {s : ℂ | ‖s‖ < 1})
    (hreal : ∀ x : ℝ, 0 < x → x < 1/16 → f (x:ℂ)=g (x:ℂ)) :
    EqOn f g {s : ℂ | ‖s‖ < 1} := by
  have hconn : IsPreconnected {s : ℂ | ‖s‖ < 1} := by
    simpa only [Metric.ball, dist_zero_right] using
      (convex_ball (0:ℂ) (1:ℝ)).isPreconnected
  have hpoint : ((1/32:ℝ):ℂ) ∈ {s : ℂ | ‖s‖ < 1} := by
    norm_num
  have ht : Tendsto (fun x : ℝ => (x:ℂ))
      (𝓝[>] (1/32:ℝ)) (𝓝[≠] ((1/32:ℝ):ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨Complex.continuous_ofReal.continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    change (x:ℂ) ∉ ({((1/32:ℝ):ℂ)} : Set ℂ)
    simp only [mem_singleton_iff, Complex.ofReal_inj]
    exact hx.ne'
  have hsmall : ∀ᶠ x : ℝ in 𝓝[>] (1/32:ℝ), x < 1/16 :=
    (eventually_lt_nhds (by norm_num : (1/32:ℝ) < 1/16)).filter_mono
      nhdsWithin_le_nhds
  have hfreq : ∃ᶠ x : ℝ in 𝓝[>] (1/32:ℝ), f (x:ℂ)=g (x:ℂ) := by
    apply Filter.Eventually.frequently
    filter_upwards [self_mem_nhdsWithin, hsmall] with x hx hxsmall
    exact hreal x (lt_trans (by norm_num : (0:ℝ) < 1/32) hx) hxsmall
  exact hf.eqOn_of_preconnected_of_frequently_eq hg hconn hpoint
    (ht.frequently hfreq)

end
end IsingBulk.HT.Final
