import IsingBulk.Tail.SelectorCutoffs
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! Exact geometric setup for the source retraction. These fields describe
only fixed bumps, with a constructed instance below. No contour theorem or
bound is a premise of this structure. -/
namespace IsingBulk.Tail
noncomputable section
open Filter Set
open scoped Topology ContDiff

 structure RegularSelector (f : SelectorFunctions) : Prop where
  p_smooth : ContDiff ℝ ∞ f.p
  m_smooth : ContDiff ℝ ∞ f.m
  a_smooth : ContDiff ℝ ∞ f.a
  p_nonneg : ∀ x, 0 ≤ f.p x
  m_nonneg : ∀ x, 0 ≤ f.m x
  m_le_one : ∀ x, f.m x ≤ 1
  p_zero : ∀ x, Real.sin x ≤ 0 → f.p x=0
  m_zero : ∀ x, 0 ≤ Real.sin x → f.m x=0
  p_periodic : Function.Periodic f.p (2*Real.pi)
  m_periodic : Function.Periodic f.m (2*Real.pi)
  a_periodic : Function.Periodic f.a (2*Real.pi)
  named : ∀ x, deriv f.a x ≠ 0 →
    f.p x=1 ∧ deriv f.p x=0 ∧ f.m x=0 ∧ deriv f.m x=0

 theorem constructedSelector_regular (b η α : ℝ) (hb : 0 < Real.sin b)
    (hη : 0 < η) (hηsmall : η ≤ Real.sin b/4) (hα : 0 < α) :
    RegularSelector (constructedSelector b η α) := by
  constructor
  · exact periodicUpperP_smooth α
  · exact periodicLowerM_smooth b η
  · exact periodicUpperA_smooth α
  · intro x; exact (thresholdStep_range _ _ _).1
  · intro x; exact Real.smoothTransition.nonneg _
  · intro x; exact Real.smoothTransition.le_one _
  · intro x hx
    exact thresholdStep_zero (by linarith) (by linarith)
  · intro x hx
    exact lowerM_zero_of_nonneg_sine b η x hb hη hηsmall hx
  · intro x; exact (constructedSelector_periodic b η α x).2.1
  · intro x; exact (constructedSelector_periodic b η α x).2.2
  · intro x; exact (constructedSelector_periodic b η α x).1
  · intro x hx
    have hs : x ∈ tsupport (periodicUpperA α) := support_deriv_subset hx
    have hp := upperP_plateau_on_a_support α hα x hs
    have hm := lowerM_zero_near_a_support b η α x hb hη hηsmall hα hs
    exact ⟨hp.eq_of_nhds, by simpa [constructedSelector] using hp.deriv_eq,
      hm.eq_of_nhds, by simpa [constructedSelector] using hm.deriv_eq⟩

 theorem periodic_derivative {f : ℝ → ℝ} {T : ℝ} (hf : Function.Periodic f T) :
    Function.Periodic (deriv f) T := by
  intro x
  have he : (fun u => f (u+T)) = f := funext hf
  rw [← deriv_comp_add_const f T x,he]

end
end IsingBulk.Tail
