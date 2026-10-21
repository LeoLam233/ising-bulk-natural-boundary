import IsingBulk.First.RegularMeanSeparatedIntegrals
import IsingBulk.First.MeanRegularError

/-! Sign-independent regular phase foundation for the actual source. -/
namespace IsingBulk.First.Regular
noncomputable section
open Complex Filter Set IsingBulk.Branch
open scoped Topology BigOperators

theorem actual_displaced_mean_sides_bounds (a : RegularChartData) (n : ℕ)
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
theorem actual_mean_cutoff_edges_bounds (a : RegularChartData) (n : ℕ)
    (halpha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I)=1)
    (hbeta : exp (-(n+1:ℂ)*(a.beta:ℂ)*I)=1) :
    ∃ D : ℝ, 0 < D ∧ ∀ delta : ℝ, 0 < delta → delta ≤ D →
      ∃ r : ℝ, 0 < r ∧ ∀ eta : ℝ → ℂ, Continuous eta →
      (∀ (rho : ℝ) (t : Fin n → ℝ), ‖(rho,t)‖ ≤ r → ∀ s : ℂ,
        ‖s-exp ((a.theta:ℂ)*I)‖ < r →
        AnalyticAt ℂ (fun z => meanCutoffEdges eta z rho a.alpha delta t) s) ∧
      (∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (rho : ℝ) (t : Fin n → ℝ), ‖(rho,t)‖ ≤ r →
        ∀ s : ℂ, ‖s-exp ((a.theta:ℂ)*I)‖ < r →
        ‖(deriv^[j] (fun z => meanCutoffEdges eta z rho a.alpha delta t)) s‖ ≤ C) := by
  obtain ⟨D,hD,hTube⟩ := actual_mean_separated_integrals a n halpha hbeta
  refine ⟨D,hD,?_⟩
  intro delta hd hdD
  obtain ⟨r,hr,hInt⟩ := hTube delta hd hdD
  refine ⟨r,hr,?_⟩
  intro eta heta
  have hL := hInt (Icc (-2*delta) (-delta)) isCompact_Icc (fun x : ℝ => (x:ℂ))
    Complex.continuous_ofReal (meanLeftEdge_annulus hd) eta heta.continuousOn
  have hR := hInt (Icc delta (2*delta)) isCompact_Icc (fun x : ℝ => (x:ℂ))
    Complex.continuous_ofReal (meanRightEdge_annulus hd) eta heta.continuousOn
  constructor
  · intro rho t ht s hs
    exact (hL.1 rho t ht s hs).add (hR.1 rho t ht s hs)
  · intro j
    obtain ⟨CL,hCL,hl⟩ := hL.2.2 j
    obtain ⟨CR,hCR,hr'⟩ := hR.2.2 j
    refine ⟨CL+CR,by positivity,?_⟩
    intro rho t ht s hs
    have haL := hL.1 rho t ht s hs
    have haR := hR.1 rho t ht s hs
    simp only [← iteratedDeriv_eq_iterate] at *
    unfold meanCutoffEdges
    rw [iteratedDeriv_fun_add haL.contDiffAt haR.contDiffAt]
    exact (norm_add_le _ _).trans (add_le_add (hl rho t ht s hs) (hr' rho t ht s hs))
theorem actual_mean_regular_error_bounds (a : RegularChartData) (n : ℕ)
    (halpha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I)=1)
    (hbeta : exp (-(n+1:ℂ)*(a.beta:ℂ)*I)=1) :
    ∃ D : ℝ, 0 < D ∧ ∀ delta : ℝ, 0 < delta → delta ≤ D →
      ∃ r : ℝ, 0 < r ∧ ∀ eta : ℝ → ℂ, Continuous eta →
      (∀ (rho : ℝ) (t : Fin n → ℝ), ‖(rho,t)‖ ≤ r → ∀ s : ℂ,
        ‖s-exp ((a.theta:ℂ)*I)‖ < r →
        AnalyticAt ℂ (fun z => meanRegularError eta z rho a.alpha delta t) s) ∧
      (∀ j : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (rho : ℝ) (t : Fin n → ℝ), ‖(rho,t)‖ ≤ r →
        ∀ s : ℂ, ‖s-exp ((a.theta:ℂ)*I)‖ < r →
        ‖(deriv^[j] (fun z => meanRegularError eta z rho a.alpha delta t)) s‖ ≤ C) := by
  obtain ⟨Ds,hDs,hS⟩ := actual_displaced_mean_sides_bounds a n halpha hbeta
  obtain ⟨De,hDe,hE⟩ := actual_mean_cutoff_edges_bounds a n halpha hbeta
  refine ⟨min Ds De,lt_min hDs hDe,?_⟩
  intro delta hd hdD
  obtain ⟨rs,hrs,haS,hbS⟩ := hS delta hd (hdD.trans (min_le_left _ _))
  obtain ⟨re,hre,hE'⟩ := hE delta hd (hdD.trans (min_le_right _ _))
  refine ⟨min rs re,lt_min hrs hre,?_⟩
  intro eta heta
  obtain ⟨haE,hbE⟩ := hE' eta heta
  have hAnalytic (rho : ℝ) (t : Fin n → ℝ) (ht : ‖(rho,t)‖ ≤ min rs re) (s : ℂ)
      (hs : ‖s-exp ((a.theta:ℂ)*I)‖ < min rs re) :
      AnalyticAt ℂ (fun z => displacedMeanSides z rho a.alpha delta delta t) s ∧
      AnalyticAt ℂ (fun z => meanCutoffEdges eta z rho a.alpha delta t) s :=
    ⟨haS rho t (ht.trans (min_le_left _ _)) s (hs.trans_le (min_le_left _ _)),
      haE rho t (ht.trans (min_le_right _ _)) s (hs.trans_le (min_le_right _ _))⟩
  constructor
  · intro rho t ht s hs
    exact (hAnalytic rho t ht s hs).1.add (hAnalytic rho t ht s hs).2
  · intro j
    obtain ⟨Cs,hCs,hbs⟩ := hbS j
    obtain ⟨Ce,hCe,hbe⟩ := hbE j
    refine ⟨Cs+Ce,by positivity,?_⟩
    intro rho t ht s hs
    obtain ⟨haS',haE'⟩ := hAnalytic rho t ht s hs
    simp only [← iteratedDeriv_eq_iterate] at *
    unfold meanRegularError
    rw [iteratedDeriv_fun_add haS'.contDiffAt haE'.contDiffAt]
    exact (norm_add_le _ _).trans (add_le_add
      (hbs rho t (ht.trans (min_le_left _ _)) s (hs.trans_le (min_le_left _ _)))
      (hbe rho t (ht.trans (min_le_right _ _)) s (hs.trans_le (min_le_right _ _))))

end
end IsingBulk.First.Regular
