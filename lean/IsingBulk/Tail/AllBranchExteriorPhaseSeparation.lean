import IsingBulk.Tail.OriginalMicrocoreChart
import IsingBulk.Tail.MicrocorePhaseNeighborhood
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue

/-! Uniform physical phase separation, including both sides of the branch.
It follows from the real angular W slope and bounded analytic cosine jets. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Branch IsingBulk.Jets Set Filter Metric
open scoped Topology

theorem angularG_real_margin (b : ℝ) (hb : 0 < Real.sin b) :
    ∃ r : ℝ, 0 < r ∧ ∀ v u : ℝ, |u| ≤ r → Real.sin b/2 ≤ (angularG v b (u:ℂ)).re := by
  have hc : ContinuousAt (fun u : ℝ => Real.sin (b-u)) 0 := by fun_prop
  have he : ∀ᶠ u in 𝓝 (0:ℝ), Real.sin b/2 < Real.sin (b-u) :=
    continuousAt_const.eventually_lt hc (by simpa using half_lt_self hb)
  obtain ⟨R,hR,hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨R/2,by positivity,?_⟩
  intro v u hu
  have hs : Real.sin b/2 ≤ Real.sin (b-u) :=
    (hball (by simpa [Real.dist_eq] using hu.trans_lt (half_lt_self hR))).le
  have hform : (angularG v b (u:ℂ)).re=Real.cosh v*Real.sin (b-u) := by
    rw [angularG_real_re,Real.cosh_eq]
    rw [show b-u=-(u-b) by ring,Real.sin_neg]
    ring
  rw [hform]
  exact hs.trans (le_mul_of_one_le_left (by linarith) (Real.one_le_cosh v))

theorem angularW_lower_separation (b : ℝ) (hb : 0 < Real.sin b) :
    ∃ a r : ℝ, 0 < a ∧ 0 < r ∧ ∀ s : ℂ, ∀ v u w : ℝ,
      |u| ≤ r → |w| ≤ r → a*|u-w| ≤ ‖chartW s v b (u:ℂ)-chartW s v b (w:ℂ)‖ := by
  obtain ⟨r,hr,hG⟩ := angularG_real_margin b hb
  refine ⟨Real.sin b/2,r,by positivity,hr,?_⟩
  intro s v u w hu hw
  have hordered : ∀ u w : ℝ, |u| ≤ r → |w| ≤ r → u < w →
      (Real.sin b/2)*(w-u) ≤ ‖chartW s v b (u:ℂ)-chartW s v b (w:ℂ)‖ := by
    intro u w hu hw huw
    let f : ℝ → ℝ := fun x => (chartW s v b (x:ℂ)).re
    have hdiff (x : ℝ) : HasDerivAt f (-(angularG v b (x:ℂ)).re) x := by
      have hh := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (chartW_angular s v b (x:ℂ)).comp_ofReal
      convert! hh using 1
    obtain ⟨x,hx,he⟩ := exists_deriv_eq_slope f huw
      (fun x _ => (hdiff x).continuousAt.continuousWithinAt)
      (fun x _ => (hdiff x).differentiableAt.differentiableWithinAt)
    have hxr : |x| ≤ r := abs_le.mpr ⟨(abs_le.mp hu).1.trans hx.1.le,hx.2.le.trans (abs_le.mp hw).2⟩
    have hg := hG v x hxr
    rw [(hdiff x).deriv] at he
    have hmul : (f w-f u)=(-(angularG v b (x:ℂ)).re)*(w-u) :=
      ((eq_div_iff (sub_ne_zero.mpr huw.ne')).mp he).symm
    have hl : (Real.sin b/2)*(w-u) ≤ f u-f w := by nlinarith
    have hn := Complex.re_le_norm (chartW s v b (u:ℂ)-chartW s v b (w:ℂ))
    simpa only [Complex.sub_re] using hl.trans hn
  rcases lt_trichotomy u w with h|h|h
  · simpa only [abs_of_neg (sub_neg.mpr h),neg_sub] using hordered u w hu hw h
  · subst w; simp
  · have hh := hordered w u hw hu h
    rw [norm_sub_rev] at hh
    simpa only [abs_of_pos (sub_pos.mpr h)] using hh

theorem complex_cos_unit_lipschitz :
    ∃ C : ℝ, 0 < C ∧ ∀ z w : ℂ, ‖z‖ ≤ 1 → ‖w‖ ≤ 1 →
      ‖Complex.cos z-Complex.cos w‖ ≤ C*‖z-w‖ := by
  obtain ⟨M,hM⟩ := (isCompact_closedBall (0:ℂ) 1).exists_bound_of_continuousOn Complex.continuous_sin.continuousOn
  let C := max 1 M
  refine ⟨C,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro z w hz hw
  apply Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℂ) (f := Complex.cos)
    (s := closedBall (0:ℂ) 1) (x := w) (y := z)
    (fun t _ => Complex.differentiable_cos t) _ (convex_closedBall _ _)
    (by simpa [mem_closedBall,dist_zero_right] using hw) (by simpa [mem_closedBall,dist_zero_right] using hz)
  intro t ht
  rw [Complex.deriv_cos,norm_neg]
  exact (hM t ht).trans (le_max_right _ _)

theorem original_phase_difference_lower (d : LocalBranchData) :
    ∃ c r : ℝ, 0 < c ∧ 0 < r ∧ ∀ ε u v : ℝ,
      0 < ε → ε ≤ r → |u| ≤ r → |v| ≤ r →
      c*|u-v| ≤ ‖originalPhase d ε u-originalPhase d ε v‖ := by
  obtain ⟨a,rW,ha,hrW,hW⟩ := angularW_lower_separation d.thetaB d.a_pos
  obtain ⟨rP,Cp,hrP,_,hP⟩ := original_phase_small_radius d 1 zero_lt_one
  obtain ⟨C,hC,hcos⟩ := complex_cos_unit_lipschitz
  let r := min rW rP/2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrW' : r ≤ rW := (half_le_self (le_min hrW.le hrP.le)).trans (min_le_left _ _)
  have hrP' : r < rP := (half_lt_self (lt_min hrW hrP)).trans_le (min_le_right _ _)
  refine ⟨a/C,r,by positivity,hr,?_⟩
  intro ε u v hε hεr hu hv
  have hpu := (hP ε r u hε hεr hrP' hu).2.le
  have hpv := (hP ε r v hε hεr hrP' hv).2.le
  have hh := hcos (originalPhase d ε u) (originalPhase d ε v) hpu hpv
  have hwu := hW (radialParameter d.theta ε) (-d.c₀*ε) u v (hu.trans hrW') (hv.trans hrW')
  rw [original_chartW_eq,original_chartW_eq] at hwu
  have hco : ∀ t, Complex.cos (originalPhase d ε t)=originalW d ε t := fun _ => cos_lowerArccos _
  rw [hco u,hco v] at hh
  have hn := hwu.trans hh
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hC).mpr
  nlinarith

end
end IsingBulk.Tail
