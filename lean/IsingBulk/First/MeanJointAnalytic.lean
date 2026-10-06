import IsingBulk.First.ActualDensityAnalytic
import IsingBulk.First.MeanMotion

/-! The complete mean density as a literal jointly complex analytic quotient.
Both global product denominators are retained, and the fixed angular cutoff is absent. -/
namespace IsingBulk.First
noncomputable section
open Complex
open scoped BigOperators Topology
attribute [local fun_prop] analyticAt_fst analyticAt_snd

def complexMeanYDenominator {N : ℕ} (alpha : ℝ) (p : ℂ × (Fin N → ℂ)) : ℂ :=
  1-coordinateProduct (complexDensityY alpha p.2)

def complexMeanNumerator {N : ℕ} (alpha : ℝ) (p : ℂ × (Fin N → ℂ)) : ℂ :=
  ((coordinateProduct (complexDensityZ alpha p))⁻¹+(coordinateProduct (complexDensityY alpha p.2))⁻¹)*
    pairProduct (complexDensityZ alpha p)*pairProduct (complexDensityY alpha p.2)*
    (∏ j, residueFactor (complexDensityZ alpha p j)) *
    (∏ j, complexDensityY alpha p.2 j/(2*(Real.pi:ℂ)))

def complexMeanFullDensity {N : ℕ} (alpha : ℝ) (p : ℂ × (Fin N → ℂ)) : ℂ :=
  reducedDensity (complexDensityZ alpha p) (complexDensityY alpha p.2)*
    (∏ j, complexDensityY alpha p.2 j/(2*(Real.pi:ℂ)))

theorem complexMeanFullDensity_eq_quotient {N : ℕ} (alpha : ℝ) (p : ℂ × (Fin N → ℂ)) :
    complexMeanFullDensity alpha p = complexMeanNumerator alpha p /
      (complexDensityDenominator alpha p*complexMeanYDenominator alpha p) := by
  unfold complexMeanFullDensity complexMeanNumerator reducedDensity complexDensityDenominator
    complexMeanYDenominator coordinateProduct
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem complexMeanYDenominator_analyticAt {N : ℕ} (alpha : ℝ) (p : ℂ × (Fin N → ℂ)) :
    AnalyticAt ℂ (complexMeanYDenominator alpha) p :=
  analyticAt_const.sub (Finset.univ.analyticAt_fun_prod (fun j _ => complexDensityY_analyticAt alpha j p))

private theorem pairProduct_analyticAt_family {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {N : ℕ} {z : E → Fin N → ℂ} {p : E}
    (hz : ∀ j, AnalyticAt ℂ (fun q => z q j) p)
    (hne : ∀ i j, 1-z p i*z p j ≠ 0) : AnalyticAt ℂ (fun q => pairProduct (z q)) p := by
  unfold pairProduct
  exact Finset.univ.analyticAt_fun_prod (fun i _ =>
    (Finset.univ.filter (fun j => i<j)).analyticAt_fun_prod (fun j _ =>
      ((hz i).sub (hz j)).div (analyticAt_const.sub ((hz i).mul (hz j))) (hne i j)))

theorem complexMeanNumerator_analyticAt (a : OrderedChartData) (N : ℕ) :
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
theorem complexMeanFullDensity_local_analytic (a : OrderedChartData) (N : ℕ) :
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

/-- Complex coordinates corresponding exactly to a fixed-radius mean chart. -/
def meanComplexCoordinates {n : ℕ} (rho : ℝ) (t : Fin n → ℝ) (v : ℂ) : Fin (n+1) → ℂ :=
  fun j => ((shapeExtend t j:ℝ):ℂ)+v/(n+1)-I*(rho:ℂ)

theorem complexDensityY_mean_coordinates {n : ℕ} (rho alpha : ℝ) (t : Fin n → ℝ) (v : ℂ) :
    complexDensityY alpha (meanComplexCoordinates rho t v) = meanChartY rho alpha t v := by
  funext j
  unfold complexDensityY meanComplexCoordinates meanChartY IsingBulk.Jets.angularY
  congr 1
  ring_nf
  simp [I_sq]

theorem complexDensityZ_mean_coordinates {n : ℕ} (s : ℂ) (rho alpha : ℝ) (t : Fin n → ℝ) (v : ℂ) :
    complexDensityZ alpha (s,meanComplexCoordinates rho t v) = meanChartRoots s rho alpha t v := by
  funext j
  unfold complexDensityZ
  rw [complexDensityY_mean_coordinates]
  rfl

theorem complexMeanFullDensity_mean_coordinates {n : ℕ} (s : ℂ) (rho alpha : ℝ)
    (t : Fin n → ℝ) (v : ℂ) :
    complexMeanFullDensity alpha (s,meanComplexCoordinates rho t v) = meanLocalDensity s rho alpha t v := by
  unfold complexMeanFullDensity meanLocalDensity meanAngularJacobian
  rw [complexDensityY_mean_coordinates,complexDensityZ_mean_coordinates]

end
end IsingBulk.First
