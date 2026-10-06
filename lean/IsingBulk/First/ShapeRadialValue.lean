import IsingBulk.First.ShapeRadialAnalytic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecificLimits.Basic

/-! The beta closed form, with its principal branch and explicit analytic domain. -/
namespace IsingBulk.First
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

def shapeRadialValue (k : ℕ) (Q : ℝ) (c : ℂ) : ℂ :=
  (1/2 : ℂ) * (Q : ℂ)^(-1/2 : ℂ) * c^(-(k : ℂ)-1/2) *
    Complex.betaIntegral ((k : ℂ)+1/2) (1/2)

theorem shapeRadialValue_ne_zero (k : ℕ) {Q : ℝ} {c : ℂ}
    (hQ : 0 < Q) (hc : c ≠ 0) : shapeRadialValue k Q c ≠ 0 := by
  unfold shapeRadialValue
  apply mul_ne_zero _ (shapeBeta_ne_zero k)
  apply mul_ne_zero _ (Complex.cpow_ne_zero_iff.mpr (Or.inl hc))
  apply mul_ne_zero (by norm_num)
  exact Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hQ.ne'))

theorem shapeRadialValue_differentiableAt (k : ℕ) (Q : ℝ) {c : ℂ}
    (hc : c ∈ Complex.slitPlane) : DifferentiableAt ℂ (shapeRadialValue k Q) c := by
  have hd := ((hasDerivAt_id c).cpow_const (c := -(k : ℂ)-1/2) hc).differentiableAt
  exact ((differentiableAt_const _).mul hd).mul_const _

theorem shapeRadialValue_analyticOnNhd (k : ℕ) (Q : ℝ) :
    AnalyticOnNhd ℂ (shapeRadialValue k Q) {c : ℂ | 0 < c.re} := by
  apply DifferentiableOn.analyticOnNhd
  · intro c hc
    exact (shapeRadialValue_differentiableAt k Q (Or.inl hc)).differentiableWithinAt
  · exact isOpen_lt continuous_const Complex.continuous_re

theorem shapeRadialValue_boundary_continuous (k : ℕ) (Q : ℝ) {d : ℝ} (hd : 0 < d) :
    ContinuousAt (shapeRadialValue k Q) (-Complex.I*d) := by
  apply (shapeRadialValue_differentiableAt k Q _).continuousAt
  right
  simpa using neg_ne_zero.mpr hd.ne'

/-- A source-independent identity principle specialized to the connected right
half-plane; equality on all positive real coefficients suffices. -/
theorem analytic_rightHalfPlane_eq {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f {c : ℂ | 0 < c.re})
    (hg : AnalyticOnNhd ℂ g {c : ℂ | 0 < c.re})
    (hreal : ∀ c : ℝ, 0 < c → f c = g c) :
    Set.EqOn f g {c : ℂ | 0 < c.re} := by
  have hconn : IsPreconnected {c : ℂ | 0 < c.re} :=
    (convex_halfSpace_gt Complex.reCLM.toLinearMap.isLinear 0).isPreconnected
  let u : ℕ → ℝ := fun n => 1 + 1 / ((n : ℝ)+1)
  have hu : Tendsto u atTop (𝓝 1) := by
    simpa [u] using tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have ht : Tendsto (fun n => (u n : ℂ)) atTop (𝓝[≠] (1 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨Complex.continuous_ofReal.continuousAt.tendsto.comp hu, ?_⟩
    apply Eventually.of_forall
    intro n
    have hp : 0 < 1 / ((n : ℝ)+1) := by positivity
    have he : u n ≠ 1 := by dsimp [u]; linarith
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, ← Complex.ofReal_one,
      Complex.ofReal_inj] using he
  have he : ∃ᶠ n in atTop, f (u n) = g (u n) :=
    (Eventually.of_forall fun n => hreal (u n) (by dsimp [u]; positivity)).frequently
  exact hf.eqOn_of_preconnected_of_frequently_eq hg hconn (z₀ := 1) (by norm_num)
    (ht.frequently he)

end
end IsingBulk.First
