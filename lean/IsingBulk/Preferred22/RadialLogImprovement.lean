import IsingBulk.Preferred22.NonCancellation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! The exact logarithm-to-boundedness step in the final paragraph of
Lemma 10.1. It needs the next derivative's actual radial logarithmic bound;
that bound is not supplied by this module. The coefficient specialization
uses the already proved exterior analyticity, so there is no new analytic
continuation premise on the physical coefficient. -/
namespace IsingBulk.Preferred22
noncomputable section
open Set MeasureTheory
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The radial fundamental theorem of calculus turns an integrable
logarithmic bound on derivative j+1 into a uniform bound on derivative j.
No boundary value or extension at epsilon=0 is assumed. -/
theorem preferred_radial_log_improvement {R : ℂ → ℂ} {ζ : ℂ}
    (hζ : ‖ζ‖=1) {a C : ℝ} (_ha : 0<a) (hC : 0≤C) (j : ℕ)
    (hR : ∀ t : ℝ, 0<t → t≤a → AnalyticAt ℂ R ((1+(t:ℂ))*ζ))
    (hnext : ∀ t : ℝ, 0<t → t≤a →
      ‖iteratedDeriv (j+1) R ((1+(t:ℂ))*ζ)‖ ≤ C*(1+|Real.log t|)) :
    ∃ M : ℝ, 0<M ∧ ∀ ε : ℝ, 0<ε → ε≤a →
      ‖iteratedDeriv j R ((1+(ε:ℂ))*ζ)‖≤M := by
  let g : ℝ → ℂ := fun t => iteratedDeriv j R ((1+(t:ℂ))*ζ)
  let g' : ℝ → ℂ := fun t => ζ*iteratedDeriv (j+1) R ((1+(t:ℂ))*ζ)
  let b : ℝ → ℝ := fun t => C*(1+|Real.log t|)
  have hbi (x y : ℝ) : IntervalIntegrable b volume x y := by
    simpa only [b,Real.norm_eq_abs] using
      (intervalIntegrable_const.add (intervalIntegral.intervalIntegrable_log'.norm)).const_mul C
  have hb (t : ℝ) : 0≤b t := mul_nonneg hC (by positivity)
  have hpath : Continuous (fun t : ℝ => (1+(t:ℂ))*ζ) := by fun_prop
  have hgd (t : ℝ) (ht : 0<t) (hta : t≤a) : HasDerivAt g (g' t) t := by
    have hd := (IsingBulk.First.analyticAt_iteratedDeriv (hR t ht hta) j).differentiableAt.hasDerivAt
    have hp : HasDerivAt (fun z : ℂ => (1+z)*ζ) ζ (t:ℂ) := by
      simpa using ((hasDerivAt_id (t:ℂ)).const_add 1).mul_const ζ
    convert! (hd.comp (t:ℂ) hp).comp_ofReal using 1
    simp only [g',iteratedDeriv_succ,mul_comm]
  have hgc (t : ℝ) (ht : 0<t) (hta : t≤a) : ContinuousAt g' t := by
    have hc := (IsingBulk.First.analyticAt_iteratedDeriv (hR t ht hta) (j+1)).continuousAt
    exact continuousAt_const.mul (hc.comp (f := fun t : ℝ => (1+(t:ℂ))*ζ) (x := t) hpath.continuousAt)
  refine ⟨‖g a‖+|∫ t in (0:ℝ)..a,b t|+1,by positivity,?_⟩
  intro ε hε hεa
  have hi : IntervalIntegrable g' volume ε a := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le hεa] at ht
    exact (hgc t (hε.trans_le ht.1) ht.2).continuousWithinAt
  have hftc : (∫ t in ε..a,g' t)=g a-g ε :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => by
      rw [uIcc_of_le hεa] at ht
      exact hgd t (hε.trans_le ht.1) ht.2) hi
  have hmass : ‖∫ t in ε..a,g' t‖≤∫ t in ε..a,b t := by
    apply intervalIntegral.norm_integral_le_of_norm_le hεa _ (hbi ε a)
    filter_upwards [] with t ht
    simpa only [g',b,norm_mul,hζ,one_mul] using hnext t (hε.trans ht.1) ht.2
  have hmono : (∫ t in ε..a,b t)≤∫ t in (0:ℝ)..a,b t :=
    intervalIntegral.integral_mono_interval hε.le hεa le_rfl
      (Filter.Eventually.of_forall hb) (hbi 0 a)
  calc
    ‖iteratedDeriv j R ((1+(ε:ℂ))*ζ)‖ = ‖g ε‖ := rfl
    _ ≤ ‖g a‖+‖g a-g ε‖ := by
      calc
        _ = ‖g a-(g a-g ε)‖ := by congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    _ ≤ ‖g a‖+|∫ t in (0:ℝ)..a,b t|+1 := by
      rw [← hftc]
      have hh := hmass.trans (hmono.trans (le_abs_self _))
      linarith

/-- Literal complete constrained coefficient version of Lemma 10.1's
last step, with all exterior analyticity hypotheses discharged. The sole
remaining estimate is the next derivative's actual logarithmic bound. -/
theorem preferred_coefficient_log_improvement (N j : ℕ) {ζ : ℂ} (hζ : ‖ζ‖=1)
    {a C : ℝ} (ha : 0<a) (hC : 0≤C)
    (hnext : ∀ t : ℝ, 0<t → t≤a →
      ‖iteratedDeriv (j+1) (coefficient N) ((1+(t:ℂ))*ζ)‖≤C*(1+|Real.log t|)) :
    ∃ M : ℝ, 0<M ∧ ∀ ε : ℝ, 0<ε → ε≤a →
      ‖iteratedDeriv j (coefficient N) ((1+(ε:ℂ))*ζ)‖≤M := by
  apply preferred_radial_log_improvement hζ ha hC j _ hnext
  intro t ht _
  exact coefficient_analyticAt N (radialPath_exterior hζ ht)

end
end IsingBulk.Preferred22
