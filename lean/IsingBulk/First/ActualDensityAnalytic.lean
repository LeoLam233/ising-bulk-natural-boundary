import IsingBulk.First.ActualDensityCenter
import IsingBulk.First.JointPoleRegularity

/-! Joint complex analyticity of the genuine branch/rational density, before
restricting to the real zero-sum shape chart. The fixed real sinc factor stays outside. -/
namespace IsingBulk.First
noncomputable section
open Complex
open scoped BigOperators Topology
attribute [local fun_prop] analyticAt_fst analyticAt_snd

def complexDensityY {N : ℕ} (alpha : ℝ) (u : Fin N → ℂ) (j : Fin N) : ℂ :=
  exp ((u j-(alpha:ℂ))*I)

def complexDensityZ {N : ℕ} (alpha : ℝ) (p : ℂ × (Fin N → ℂ)) (j : Fin N) : ℂ :=
  phaseRoot (sourceW p.1 (complexDensityY alpha p.2 j))

def complexDensityDenominator {N : ℕ} (alpha : ℝ) (p : ℂ × (Fin N → ℂ)) : ℂ :=
  1-∏ j, complexDensityZ alpha p j

def complexDensityRegular {N : ℕ} (alpha : ℝ) (p : ℂ × (Fin N → ℂ)) : ℂ :=
  ((∏ j, complexDensityZ alpha p j)⁻¹+1) *
    (∏ ij ∈ firstStrictPairs N,
      complexDensityZ alpha p ij.1 * complexDensityZ alpha p ij.2 /
        (1-complexDensityZ alpha p ij.1*complexDensityZ alpha p ij.2)^2) *
    (∏ j, residueFactor (complexDensityZ alpha p j)) *
    (∏ j, complexDensityY alpha p.2 j/(2*(Real.pi:ℂ)))

theorem complexDensityY_analyticAt {N : ℕ} (alpha : ℝ) (j : Fin N)
    (c : ℂ × (Fin N → ℂ)) :
    AnalyticAt ℂ (fun p : ℂ × (Fin N → ℂ) => complexDensityY alpha p.2 j) c := by
  have he : AnalyticAt ℂ (fun p : ℂ × (Fin N → ℂ) => p.2 j) c :=
    (((ContinuousLinearMap.proj j : (Fin N → ℂ) →L[ℂ] ℂ).comp
      (ContinuousLinearMap.snd ℂ ℂ (Fin N → ℂ))).analyticAt c)
  exact ((he.sub analyticAt_const).mul analyticAt_const).cexp

@[simp] theorem complexDensityZ_center (a : OrderedChartData) (N : ℕ) (j : Fin N) :
    complexDensityZ a.alpha (exp ((a.theta:ℂ)*I),(0 : Fin N → ℂ)) j =
      exp (-(a.beta:ℂ)*I) := by
  simp only [complexDensityZ, complexDensityY, Pi.zero_apply, zero_sub,
    sourceW_density_center, phaseRoot]
  rw [lowerArccos_cos a.beta a.beta_pos (by linarith [a.beta_lt, Real.pi_pos])]
  congr 1
  ring

theorem complexDensityZ_analyticAt (a : OrderedChartData) (N : ℕ) (j : Fin N) :
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
    (lowerArccos_analytic_cos a.beta a.beta_pos a.beta_lt).comp_of_eq hw he
  unfold complexDensityZ phaseRoot
  exact (analyticAt_const.mul hp).cexp

theorem complexDensityDenominator_analyticAt (a : OrderedChartData) (N : ℕ) :
    AnalyticAt ℂ (@complexDensityDenominator N a.alpha)
      (exp ((a.theta:ℂ)*I),(0 : Fin N → ℂ)) := by
  exact analyticAt_const.sub (Finset.univ.analyticAt_fun_prod
    (fun j _ => complexDensityZ_analyticAt a N j))

theorem complexDensityRegular_analyticAt (a : OrderedChartData) (N : ℕ) :
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

/-- Exact pullback along the source zero-sum chart, without changing the
source parameter or the fixed shape weight. -/
theorem complexDensityRegular_real_shape {n : ℕ} (s : ℂ) (alpha : ℝ) (t : Fin n → ℝ) :
    complexDensityRegular alpha (s,fun j => ((shapeExtend t j:ℝ):ℂ)) =
      actualRegularFactor s alpha t := by rfl

theorem complexDensityDenominator_real_shape {n : ℕ} (s : ℂ) (alpha : ℝ) (t : Fin n → ℝ) :
    complexDensityDenominator alpha (s,fun j => ((shapeExtend t j:ℝ):ℂ)) =
      shapePoleDenominator s alpha t := by rfl

end
end IsingBulk.First
