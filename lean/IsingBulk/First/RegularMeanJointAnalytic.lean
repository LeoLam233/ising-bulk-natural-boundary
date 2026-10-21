import IsingBulk.First.RegularDensityAnalytic
import IsingBulk.First.MeanJointAnalytic

/-! Sign-independent regular phase foundation for the actual source. -/
namespace IsingBulk.First.Regular
noncomputable section
open Complex Filter Set IsingBulk.Branch
open scoped Topology BigOperators

private theorem pairProduct_analyticAt_family {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {N : ℕ} {z : E → Fin N → ℂ} {p : E}
    (hz : ∀ j, AnalyticAt ℂ (fun q => z q j) p)
    (hne : ∀ i j, 1-z p i*z p j ≠ 0) : AnalyticAt ℂ (fun q => pairProduct (z q)) p := by
  unfold pairProduct
  exact Finset.univ.analyticAt_fun_prod (fun i _ =>
    (Finset.univ.filter (fun j => i<j)).analyticAt_fun_prod (fun j _ =>
      ((hz i).sub (hz j)).div (analyticAt_const.sub ((hz i).mul (hz j))) (hne i j)))

theorem complexMeanNumerator_analyticAt (a : RegularChartData) (N : ℕ) :
    AnalyticAt ℂ (@complexMeanNumerator N a.alpha)
      (exp ((a.theta:ℂ)*I),(0 : Fin N → ℂ)) := by
  let p : ℂ × (Fin N → ℂ) := (exp ((a.theta:ℂ)*I),0)
  have hy (j : Fin N) := complexDensityY_analyticAt a.alpha j p
  have hz (j : Fin N) : AnalyticAt ℂ (fun q => complexDensityZ a.alpha q j) p :=
    complexDensityZ_analyticAt a N j
  have hY := Finset.univ.analyticAt_fun_prod (fun j _ => hy j)
  have hZ := Finset.univ.analyticAt_fun_prod (fun j _ => hz j)
  have hY0 : (∏ j, complexDensityY a.alpha p.2 j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => exp_ne_zero _)
  have hZ0 : (∏ j, complexDensityZ a.alpha p j) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => phaseRoot_ne_zero _)
  have hpy (i j : Fin N) : 1-complexDensityY a.alpha p.2 i*complexDensityY a.alpha p.2 j ≠ 0 := by
    dsimp [p,complexDensityY]
    simp only [zero_sub]
    rw [← pow_two]
    exact one_sub_negative_angle_sq_ne_zero a.sin_alpha_pos.ne'
  have hpz (i j : Fin N) : 1-complexDensityZ a.alpha p i*complexDensityZ a.alpha p j ≠ 0 := by
    dsimp [p]
    rw [complexDensityZ_center,complexDensityZ_center,← pow_two]
    exact one_sub_negative_angle_sq_ne_zero a.sin_beta_pos.ne'
  have hPairY := pairProduct_analyticAt_family hy hpy
  have hPairZ := pairProduct_analyticAt_family hz hpz
  have hR := Finset.univ.analyticAt_fun_prod (fun j _ =>
    ((analyticAt_const (v := (2:ℂ))).mul ((hz j).pow 2)).div
      (analyticAt_const.sub ((hz j).pow 2)) (by simpa only [pow_two,Pi.sub_apply,Pi.mul_apply] using! hpz j j))
  have hJ := Finset.univ.analyticAt_fun_prod (fun j _ => (hy j).div_const (c := 2*(Real.pi:ℂ)))
  exact ((((hZ.inv hZ0).add (hY.inv hY0)).mul hPairZ).mul hPairY).mul hR |>.mul hJ

/-- On a fixed neighborhood, only the two displayed global products can
obstruct joint analyticity; all local branch/pair factors are already proved regular. -/
theorem complexMeanFullDensity_local_analytic (a : RegularChartData) (N : ℕ) :
    ∃ r : ℝ, 0 < r ∧ ∀ p : ℂ × (Fin N → ℂ),
      ‖p-(exp ((a.theta:ℂ)*I),0)‖ < r →
      complexDensityDenominator a.alpha p ≠ 0 → complexMeanYDenominator a.alpha p ≠ 0 →
      AnalyticAt ℂ (complexMeanFullDensity a.alpha) p := by
  have hb := (complexMeanNumerator_analyticAt a N).eventually_analyticAt
  have hd := (complexDensityDenominator_analyticAt a N).eventually_analyticAt
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp (hb.and hd)
  refine ⟨r,hr,?_⟩
  intro p hp hZ hY
  have hh := hball (by simpa [dist_eq_norm] using hp)
  have ha := hh.1.div (hh.2.mul (complexMeanYDenominator_analyticAt a.alpha p)) (mul_ne_zero hZ hY)
  exact ha.congr (Filter.Eventually.of_forall (fun q => (complexMeanFullDensity_eq_quotient a.alpha q).symm))

end
end IsingBulk.First.Regular
