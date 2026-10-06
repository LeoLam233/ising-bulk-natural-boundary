import IsingBulk.Tail.MicrocoreVariableAnalytic
import IsingBulk.Tail.MicrocoreChartPoint
import Mathlib.Analysis.Complex.CauchyIntegral

/-! Joint analytic complexification of the actual microcore top form.
This supplies real-spatial smoothness and compact-integral regularity. -/
namespace IsingBulk.Tail
noncomputable section
open IsingBulk.Jets IsingBulk.Lie IsingBulk.Branch Set
open scoped BigOperators
attribute [local fun_prop] analyticAt_fst analyticAt_snd

theorem lowerArccos_analytic_upper_quadrant (W : ℂ) (hr : 0 < W.re) (hi : 0 < W.im) :
    AnalyticAt ℂ lowerArccos W := by
  apply DifferentiableOn.analyticAt (s := {z : ℂ | 0 < z.re ∧ 0 < z.im})
  · intro z hz
    exact (lowerArccos_differentiable z hz.1 hz.2).differentiableWithinAt
  · exact ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)).mem_nhds ⟨hr,hi⟩

def microComplexChartMap {N : ℕ} (v θ : ℝ) (z : ℂ × (Fin N → ℂ)) : Fin N → ℂ :=
  fun i => chartPhase z.1 v θ (z.2 i)

def microComplexPullback {N : ℕ} (v θ : ℝ) (F : ℂ × (Fin N → ℂ) → ℂ)
    (z : ℂ × (Fin N → ℂ)) : ℂ :=
  (∏ i, chartB z.1 v θ (z.2 i))*F (z.1,microComplexChartMap v θ z)

theorem microComplexPullback_analytic {N : ℕ} (v θ : ℝ)
    (F : ℂ × (Fin N → ℂ) → ℂ) (z : ℂ × (Fin N → ℂ)) (hs : z.1 ≠ 0)
    (hr : ∀ i, 0 < (chartW z.1 v θ (z.2 i)).re)
    (hi : ∀ i, 0 < (chartW z.1 v θ (z.2 i)).im)
    (hn : ∀ i, Complex.sin (chartPhase z.1 v θ (z.2 i)) ≠ 0)
    (hF : AnalyticAt ℂ F (z.1,microComplexChartMap v θ z)) :
    AnalyticAt ℂ (microComplexPullback v θ F) z := by
  have hY : ∀ i, AnalyticAt ℂ (fun t : ℂ × (Fin N → ℂ) => angularY v θ (t.2 i)) z := by
    intro i
    exact (analyticAt_const.add (((analytic_coordinate i z).sub analyticAt_const).mul analyticAt_const)).cexp
  have hW : ∀ i, AnalyticAt ℂ (fun t : ℂ × (Fin N → ℂ) => chartW t.1 v θ (t.2 i)) z := by
    intro i
    exact (analyticAt_fst.add (analyticAt_fst.inv hs)).sub
      (((hY i).add ((hY i).inv (Complex.exp_ne_zero _))).div_const)
  have hp : ∀ i, AnalyticAt ℂ (fun t : ℂ × (Fin N → ℂ) => chartPhase t.1 v θ (t.2 i)) z := by
    intro i
    exact (lowerArccos_analytic_upper_quadrant _ (hr i) (hi i)).comp
      (f := fun t : ℂ × (Fin N → ℂ) => chartW t.1 v θ (t.2 i)) (hW i)
  have hG : ∀ i, AnalyticAt ℂ (fun t : ℂ × (Fin N → ℂ) => angularG v θ (t.2 i)) z := by
    intro i
    exact (analyticAt_const.mul ((hY i).sub ((hY i).inv (Complex.exp_ne_zero _)))).div_const
  have hJ : AnalyticAt ℂ (fun t : ℂ × (Fin N → ℂ) => ∏ i, chartB t.1 v θ (t.2 i)) z :=
    Finset.analyticAt_fun_prod _ (fun i _ => (hG i).div (Complex.analyticAt_sin.comp (hp i)) (hn i))
  have hc := AnalyticAt.comp (g := F)
    (f := fun t : ℂ × (Fin N → ℂ) => (t.1,microComplexChartMap v θ t))
    hF (analyticAt_fst.prod (AnalyticAt.pi hp))
  exact hJ.mul hc

theorem microcorePhaseFactor_analytic {N : ℕ} (φ : Fin N → ℂ)
    (hZ : 1-Complex.exp (-Complex.I*∑ i, φ i) ≠ 0) :
    AnalyticAt ℂ microcorePhaseFactor φ := by
  have hp : AnalyticAt ℂ (@microcoreVandermondeSquared N) φ := by
    unfold microcoreVandermondeSquared
    apply Finset.analyticAt_fun_prod
    intro i _
    apply Finset.analyticAt_fun_prod
    intro j _
    exact (((ContinuousLinearMap.proj (R := ℂ) i).analyticAt φ).sub
      ((ContinuousLinearMap.proj (R := ℂ) j).analyticAt φ)).pow 2
  have hd : AnalyticAt ℂ (fun ψ : Fin N → ℂ => 1-Complex.exp (-Complex.I*∑ i, ψ i)) φ := by
    exact analyticAt_const.sub ((analyticAt_const.mul (Finset.analyticAt_fun_sum _
      (fun i _ => (ContinuousLinearMap.proj (R := ℂ) i).analyticAt φ))).cexp)
  exact hp.div hd hZ

theorem microRegularDensity_analytic {N : ℕ} (z : ℂ × (Fin N → ℂ))
    (hF : AnalyticAt ℂ microcoreVariableFactor z) (hZ : 1-regularZProduct z.1 z.2 ≠ 0) :
    AnalyticAt ℂ (fun t : ℂ × (Fin N → ℂ) => microRegularDensity t.1 t.2) z := by
  have hp := (microcorePhaseFactor_analytic z.2 hZ).comp (f := fun t : ℂ × (Fin N → ℂ) => t.2) analyticAt_snd
  have he : (fun t : ℂ × (Fin N → ℂ) => microRegularDensity t.1 t.2)=
      (fun t => microcorePhaseFactor t.2*microcoreVariableFactor t) := by
    funext t
    exact microRegularDensity_phase_factor t.1 t.2
  rw [he]
  exact hp.mul hF

theorem microComplexPullback_real_eq {n : ℕ} (v θ : ℝ)
    (F : ℂ × (Fin (n+1) → ℂ) → ℂ) (s : ℂ) (u : AngularSpace n) :
    microComplexPullback v θ F (s,fun i => (u i:ℂ))=
      chartPullback v θ (fun t φ => F (t,φ)) s u := rfl

end
end IsingBulk.Tail
