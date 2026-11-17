import IsingBulk.AnisoF002.C03.IsotropicAnalyticFramePullback

/-!
# Every real-frame analytic descendant is the analytic descendant pullback

The identification is proved as a local equality at every recurrence
step. Thus subsequent derivatives act on the entire preceding function,
not merely on a pointwise formula or a held-constant coefficient.
-/

noncomputable section

namespace IsingBulk.AnisoF002.Isotropic

open scoped Topology BigOperators
open Set Filter Metric

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem regularTransportAmplitude_congr_germ (χ : ι → E → ℂ) (e : ι → E) (a x : E)
    (B : ι → E → ℂ) (f g : E → ℂ) (hfg : f =ᶠ[𝓝 x] g) :
    regularTransportAmplitude χ e a B f x = regularTransportAmplitude χ e a B g x := by
  have hd := hfg.fderiv_eq (𝕜 := ℝ)
  have hv := hfg.eq_of_nhds
  simp only [regularTransportAmplitude, scalarRegularParameterDerivative, scalarFrameParameter,
    scalarRegularFrameDerivative, scalarFrameApplied, scalarPartial, hd, hv]

theorem regularTransportDescendant_joint_pullback {N : ℕ}
    (χ : Fin N → (ℂ × (Fin N → ℝ)) → ℂ)
    (B : RegularJointSpace N → Fin N → ℂ) (F : RegularJointSpace N → ℂ)
    (x : ℂ × (Fin N → ℝ))
    (hχ : ∀ i, ContDiffAt ℝ 2 (χ i) x)
    (hB : AnalyticAt ℂ B (regularJointMap χ x))
    (hF : AnalyticAt ℂ F (regularJointMap χ x))
    (hdet : scalarCoordinateDet χ actualAngularDirection x ≠ 0) (n : ℕ) :
    regularTransportDescendant χ actualAngularDirection actualTimeDirection
      (fun i y => B (regularJointMap χ y) i) (fun y => F (regularJointMap χ y)) n x =
        analyticTransportDescendant B F n (regularJointMap χ x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    have hχd (i : Fin N) : DifferentiableAt ℝ (χ i) x := (hχ i).differentiableAt (by norm_num)
    have hm : ContinuousAt (regularJointMap χ) x :=
      continuousAt_fst.prodMk (continuousAt_pi.mpr (fun i => (hχd i).continuousAt))
    have hχnear : ∀ᶠ y in 𝓝 x, ∀ i, ContDiffAt ℝ 2 (χ i) y :=
      Filter.eventually_all.mpr (fun i => (hχ i).eventually (by norm_num))
    have hdnear : ∀ᶠ y in 𝓝 x, scalarCoordinateDet χ actualAngularDirection y ≠ 0 :=
      (scalarCoordinateDet_differentiableAt χ actualAngularDirection x hχ).continuousAt.eventually_ne hdet
    have hBnear : ∀ᶠ y in 𝓝 x, AnalyticAt ℂ B (regularJointMap χ y) :=
      hm.eventually hB.eventually_analyticAt
    have hFnear : ∀ᶠ y in 𝓝 x, AnalyticAt ℂ F (regularJointMap χ y) :=
      hm.eventually hF.eventually_analyticAt
    have heq : regularTransportDescendant χ actualAngularDirection actualTimeDirection
        (fun i y => B (regularJointMap χ y) i) (fun y => F (regularJointMap χ y)) n =ᶠ[𝓝 x]
        (fun y => analyticTransportDescendant B F n (regularJointMap χ y)) := by
      filter_upwards [hχnear, hdnear, hBnear, hFnear] with y hχy hdy hBy hFy
      exact ih y hχy hBy hFy hdy
    change regularTransportAmplitude χ actualAngularDirection actualTimeDirection
      (fun i y => B (regularJointMap χ y) i)
      (regularTransportDescendant χ actualAngularDirection actualTimeDirection
        (fun i y => B (regularJointMap χ y) i) (fun y => F (regularJointMap χ y)) n) x = _
    rw [regularTransportAmplitude_congr_germ χ actualAngularDirection actualTimeDirection x
      (fun i y => B (regularJointMap χ y) i) _ _ heq]
    exact regularTransportAmplitude_joint_pullback χ B (analyticTransportDescendant B F n) x
      hχd hB.differentiableAt
      (analyticTransportDescendant_analyticAt B F _ hB hF n).differentiableAt hdet

end IsingBulk.AnisoF002.Isotropic
