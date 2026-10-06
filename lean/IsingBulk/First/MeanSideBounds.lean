import IsingBulk.First.MeanSideCurves

/-! Every fixed source derivative of the three actual displaced side integrals
is uniformly bounded on one fixed parameter/radius/shape neighborhood. -/
namespace IsingBulk.First
noncomputable section
open Set Complex
open scoped Topology

theorem actual_displaced_mean_sides_bounds (a : OrderedChartData) (n : ℕ)
    (halpha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I)=1)
    (hbeta : exp (-(n+1:ℂ)*(a.beta:ℂ)*I)=1) :
    ∃ D : ℝ, 0 < D ∧ ∀ delta : ℝ, 0 < delta → delta ≤ D →
      ∃ r : ℝ, 0 < r ∧
      (∀ (rho : ℝ) (t : Fin n → ℝ), ‖(rho,t)‖ ≤ r → ∀ s : ℂ,
        ‖s-exp ((a.theta:ℂ)*I)‖ < r →
        AnalyticAt ℂ (fun z => displacedMeanSides z rho a.alpha delta delta t) s) ∧
      (∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (rho : ℝ) (t : Fin n → ℝ), ‖(rho,t)‖ ≤ r →
        ∀ s : ℂ, ‖s-exp ((a.theta:ℂ)*I)‖ < r →
        ‖(deriv^[j] (fun z => displacedMeanSides z rho a.alpha delta delta t)) s‖ ≤ C) := by
  obtain ⟨D,hD,hTube⟩ := actual_mean_separated_integrals a n halpha hbeta
  refine ⟨D,hD,?_⟩
  intro delta hd hdD
  obtain ⟨r,hr,hInt⟩ := hTube delta hd hdD
  have hB := hInt (Icc (-delta) delta) isCompact_Icc (meanBottomCurve delta)
    (by unfold meanBottomCurve; fun_prop) (meanBottomCurve_annulus hd) (fun _ => 1) continuousOn_const
  have hR := hInt (Icc (-delta) 0) isCompact_Icc (meanRightCurve delta)
    (by unfold meanRightCurve; fun_prop) (meanRightCurve_annulus hd) (fun _ => 1) continuousOn_const
  have hL := hInt (Icc (-delta) 0) isCompact_Icc (meanLeftCurve delta)
    (by unfold meanLeftCurve; fun_prop) (meanLeftCurve_annulus hd) (fun _ => 1) continuousOn_const
  simp only [one_mul] at hB hR hL
  have he (rho : ℝ) (t : Fin n → ℝ) :
      (fun z => displacedMeanSides z rho a.alpha delta delta t) =
      (fun z => meanBottomIntegral z rho a.alpha delta t + I*meanRightIntegral z rho a.alpha delta t -
        I*meanLeftIntegral z rho a.alpha delta t) :=
    funext (fun z => displacedMeanSides_eq_compact z rho a.alpha delta hd t)
  refine ⟨r,hr,?_,?_⟩
  · intro rho t ht s hs
    rw [he]
    exact ((hB.1 rho t ht s hs).add (analyticAt_const.mul (hR.1 rho t ht s hs))).sub
      (analyticAt_const.mul (hL.1 rho t ht s hs))
  · intro j
    obtain ⟨CB,hCB,hb⟩ := hB.2.2 j
    obtain ⟨CR,hCR,hr'⟩ := hR.2.2 j
    obtain ⟨CL,hCL,hl⟩ := hL.2.2 j
    refine ⟨CB+CR+CL,by positivity,?_⟩
    intro rho t ht s hs
    rw [he]
    exact analytic_three_sides_iterated_bound (hB.1 rho t ht s hs) (hR.1 rho t ht s hs)
      (hL.1 rho t ht s hs) j (hb rho t ht s hs) (hr' rho t ht s hs) (hl rho t ht s hs)

end
end IsingBulk.First
