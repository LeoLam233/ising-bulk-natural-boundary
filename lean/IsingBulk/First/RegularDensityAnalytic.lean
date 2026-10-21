import IsingBulk.First.RegularRadialPhase
import IsingBulk.First.ActualDensityAnalytic

/-! Sign-independent regular phase foundation for the actual source. -/
namespace IsingBulk.First.Regular
noncomputable section
open Complex Filter Set IsingBulk.Branch
open scoped Topology BigOperators

theorem sourceW_density_center (a : RegularChartData) :
    sourceW (exp ((a.theta:ℂ)*I)) (exp (-(a.alpha:ℂ)*I)) = (Real.cos a.beta:ℂ) := by
  have ht := IsingBulk.PrimeFamily.exp_angle_add_inv a.theta
  have ha := IsingBulk.PrimeFamily.exp_angle_add_inv (-a.alpha)
  simp only [Real.cos_neg, ofReal_neg] at ha
  have har : (Real.cos a.alpha:ℂ)+(Real.cos a.beta:ℂ)=2*(Real.cos a.theta:ℂ) := by
    exact_mod_cast a.angle_relation
  unfold sourceW sourceS
  rw [ht, ha]
  linear_combination -har

@[simp] theorem shapeZ_density_center (a : RegularChartData) (n : ℕ) (j : Fin (n+1)) :
    shapeZ (exp ((a.theta:ℂ)*I)) a.alpha (0 : Fin n → ℝ) j =
      exp (-(a.beta:ℂ)*I) := by
  unfold shapeZ
  rw [shapeY_zero_exact, sourceW_density_center, phaseRoot,
    lowerArccos_cos a.beta a.beta_pos (by linarith [a.beta_lt_pi, Real.pi_pos])]
  congr 1
  ring

@[simp] theorem complexDensityZ_center (a : RegularChartData) (N : ℕ) (j : Fin N) :
    complexDensityZ a.alpha (exp ((a.theta:ℂ)*I),(0 : Fin N → ℂ)) j =
      exp (-(a.beta:ℂ)*I) := by
  simp only [complexDensityZ, complexDensityY, Pi.zero_apply, zero_sub,
    sourceW_density_center, phaseRoot]
  rw [lowerArccos_cos a.beta a.beta_pos (by linarith [a.beta_lt_pi, Real.pi_pos])]
  congr 1
  ring

theorem complexDensityZ_analyticAt (a : RegularChartData) (N : ℕ) (j : Fin N) :
    AnalyticAt ℂ (fun p => complexDensityZ a.alpha p j)
      (exp ((a.theta:ℂ)*I),(0 : Fin N → ℂ)) := by
  let c : ℂ × (Fin N → ℂ) := (exp ((a.theta:ℂ)*I),0)
  have hy := complexDensityY_analyticAt a.alpha j c
  have hs : AnalyticAt ℂ (fun p : ℂ × (Fin N → ℂ) => sourceS p.1) c := by
    unfold sourceS
    exact analyticAt_fst.add (analyticAt_fst.inv (exp_ne_zero _))
  have hw : AnalyticAt ℂ (fun p : ℂ × (Fin N → ℂ) => sourceW p.1 (complexDensityY a.alpha p.2 j)) c := by
    unfold sourceW
    exact hs.sub ((hy.add (hy.inv (exp_ne_zero _))).div_const)
  have he : sourceW c.1 (complexDensityY a.alpha c.2 j) = (Real.cos a.beta:ℂ) := by
    simpa [c, complexDensityY] using sourceW_density_center a
  have hp : AnalyticAt ℂ (fun p : ℂ × (Fin N → ℂ) => IsingBulk.Branch.lowerArccos
      (sourceW p.1 (complexDensityY a.alpha p.2 j))) c :=
    (lowerArccos_analytic_cos_of_lt_pi a.beta a.beta_pos a.beta_lt_pi).comp_of_eq hw he
  unfold complexDensityZ phaseRoot
  exact (analyticAt_const.mul hp).cexp

theorem complexDensityDenominator_analyticAt (a : RegularChartData) (N : ℕ) :
    AnalyticAt ℂ (@complexDensityDenominator N a.alpha)
      (exp ((a.theta:ℂ)*I),(0 : Fin N → ℂ)) := by
  exact analyticAt_const.sub (Finset.univ.analyticAt_fun_prod
    (fun j _ => complexDensityZ_analyticAt a N j))

theorem complexDensityRegular_analyticAt (a : RegularChartData) (N : ℕ) :
    AnalyticAt ℂ (@complexDensityRegular N a.alpha)
      (exp ((a.theta:ℂ)*I),(0 : Fin N → ℂ)) := by
  let c : ℂ × (Fin N → ℂ) := (exp ((a.theta:ℂ)*I),0)
  have hz := complexDensityZ_analyticAt a N
  have hprod : (∏ j, complexDensityZ a.alpha c j) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact phaseRoot_ne_zero _
  have hpair (i j : Fin N) : 1-complexDensityZ a.alpha c i*complexDensityZ a.alpha c j ≠ 0 := by
    dsimp [c]
    rw [complexDensityZ_center, complexDensityZ_center, ← pow_two]
    exact one_sub_negative_angle_sq_ne_zero a.sin_beta_pos.ne'
  have hpairSq (i j : Fin N) : (1-complexDensityZ a.alpha c i*complexDensityZ a.alpha c j)^2 ≠ 0 :=
    pow_ne_zero 2 (hpair i j)
  have hres (j : Fin N) : 1-(complexDensityZ a.alpha c j)^2 ≠ 0 := by
    simpa only [pow_two] using hpair j j
  have hy (j : Fin N) := complexDensityY_analyticAt a.alpha j c
  have hz' (j : Fin N) : AnalyticAt ℂ (fun p => complexDensityZ a.alpha p j) c := hz j
  have hZ := Finset.univ.analyticAt_fun_prod (fun j _ => hz' j)
  have hP := (firstStrictPairs N).analyticAt_fun_prod (fun ij _ =>
    ((hz' ij.1).mul (hz' ij.2)).div
      ((analyticAt_const.sub ((hz' ij.1).mul (hz' ij.2))).pow 2) (hpairSq ij.1 ij.2))
  have hR := Finset.univ.analyticAt_fun_prod (fun j _ =>
    ((analyticAt_const (v := (2:ℂ))).mul ((hz' j).pow 2)).div
      (analyticAt_const.sub ((hz' j).pow 2)) (hres j))
  have hY := Finset.univ.analyticAt_fun_prod (fun j _ => (hy j).div_const (c := 2*(Real.pi:ℂ)))
  exact ((((hZ.inv hprod).add analyticAt_const).mul hP).mul hR).mul hY

end
end IsingBulk.First.Regular
