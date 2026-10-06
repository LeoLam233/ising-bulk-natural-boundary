import IsingBulk.First.MeanAnalyticTube
import IsingBulk.First.ActualShapeDenominator

/-! Actual ordinary complex parameter tubes for the post-mean shape integral.
The source nonlinear gap supplies pole exclusion on each fixed compact shape
ball before the complex neighborhood is constructed. -/
namespace IsingBulk.First
noncomputable section
open IsingBulk.Branch Complex Set Filter Metric
open scoped Topology

def complexPostMeanResidue {N : ℕ} (alpha : ℝ) (p : ℂ × (Fin N → ℂ)) : ℂ :=
  2*(Real.pi:ℂ)*complexMeanNumerator alpha p/complexDensityDenominator alpha p/(N.factorial:ℂ)

theorem complexPostMeanResidue_real_shape {n : ℕ} (s : ℂ) (alpha : ℝ) (t : Fin n → ℝ)
    (ha : exp (-(n+1:ℂ)*(alpha:ℂ)*I) = 1) :
    complexPostMeanResidue alpha (s,fun j => ((shapeExtend t j:ℝ):ℂ)) =
      postMeanDensity s alpha t/((n+1).factorial:ℂ) := by
  have hy : complexDensityY alpha (fun i => ((shapeExtend t i:ℝ):ℂ)) = shapeY alpha t := rfl
  have hz : complexDensityZ alpha (s,fun j => ((shapeExtend t j:ℝ):ℂ)) = shapeZ s alpha t := rfl
  unfold complexPostMeanResidue complexMeanNumerator
  dsimp only
  rw [hy,hz,coordinateProduct_shapeY alpha t ha]
  simp only [inv_one]
  rfl

def intrinsicComplexShape {n : ℕ} (x : ShapeSpace n) : Fin (n+1) → ℂ :=
  fun j => (x.1 j:ℂ)

theorem intrinsicComplexShape_continuous (n : ℕ) : Continuous (@intrinsicComplexShape n) := by
  apply continuous_pi
  intro j
  exact Complex.continuous_ofReal.comp ((EuclideanSpace.proj j).continuous.comp continuous_subtype_val)

theorem intrinsicComplexShape_eq {n : ℕ} (x : ShapeSpace n) :
    intrinsicComplexShape x = fun j => ((shapeExtend (intrinsicShapeCoordinates x) j:ℝ):ℂ) := by
  rw [shapeExtend_intrinsicShapeCoordinates]
  rfl

@[simp] theorem intrinsicComplexShape_zero {n : ℕ} : intrinsicComplexShape (0:ShapeSpace n) = 0 := by
  funext j
  simp [intrinsicComplexShape]

theorem complexPostMeanResidue_intrinsic {n : ℕ} (a : OrderedChartData)
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I) = 1) (s : ℂ) (x : ShapeSpace n) :
    complexPostMeanResidue a.alpha (s,intrinsicComplexShape x) =
      postMeanDensity s a.alpha (intrinsicShapeCoordinates x)/((n+1).factorial:ℂ) := by
  rw [intrinsicComplexShape_eq]
  exact complexPostMeanResidue_real_shape s a.alpha _ ha

theorem actual_postMean_analytic_shape_tube {n : ℕ} (a : OrderedChartData)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I) = 1) :
    ∃ R : ℝ, 0 < R ∧ ∀ epsilon : ℝ, 0 < epsilon → epsilon < R →
      ∃ eta : ℝ, 0 < eta ∧ ∀ s : ℂ, ‖s-radialParameter a.theta epsilon‖ < eta →
        ∀ x : ShapeSpace n, ‖x‖ ≤ R →
          AnalyticAt ℂ (complexPostMeanResidue a.alpha) (s,intrinsicComplexShape x) := by
  let g : ℝ × ShapeSpace n → ℂ × (Fin (n+1) → ℂ) :=
    fun p => (radialParameter a.theta p.1,intrinsicComplexShape p.2)
  have hg : Continuous g := by
    apply Continuous.prodMk _ ((intrinsicComplexShape_continuous n).comp continuous_snd)
    unfold radialParameter
    fun_prop
  have hg0 : g (0,0) = (exp ((a.theta:ℂ)*I),(0:Fin (n+1) → ℂ)) := by
    simp [g,radialParameter]
  have ht := hg.tendsto (0,0)
  rw [hg0] at ht
  have hev := ht.eventually ((complexMeanNumerator_analyticAt a (n+1)).eventually_analyticAt.and
    (complexDensityDenominator_analyticAt a (n+1)).eventually_analyticAt)
  obtain ⟨rA,hrA,hA⟩ := Metric.mem_nhds_iff.mp hev
  obtain ⟨c,rD,hc,hrD,hD⟩ := actualShapeDenominator_uniform_lower (n := n) a hb
  let R := min rA rD / 2
  have hR : 0 < R := half_pos (lt_min hrA hrD)
  have hRA : R < rA := (half_lt_self (lt_min hrA hrD)).trans_le (min_le_left _ _)
  have hRD : R < rD := (half_lt_self (lt_min hrA hrD)).trans_le (min_le_right _ _)
  refine ⟨R,hR,?_⟩
  intro epsilon he heR
  have hbase (x : ShapeSpace n) (hx : x ∈ closedBall 0 R) :
      AnalyticAt ℂ (complexPostMeanResidue a.alpha) (radialParameter a.theta epsilon,intrinsicComplexShape x) := by
    have hxR : ‖x‖ ≤ R := by simpa only [mem_closedBall,dist_zero_right] using hx
    have hm : (epsilon,x) ∈ ball (0,(0:ShapeSpace n)) rA := by
      rw [mem_ball,dist_eq_norm]
      change max ‖epsilon-0‖ ‖x-0‖ < rA
      simp only [sub_zero,Real.norm_eq_abs,abs_of_pos he,max_lt_iff]
      exact ⟨heR.trans hRA,hxR.trans_lt hRA⟩
    have hh := hA hm
    have hgap := hD epsilon x he (heR.trans hRD) (hxR.trans_lt hRD)
    have hne : complexDensityDenominator a.alpha (g (epsilon,x)) ≠ 0 := by
      have heq : complexDensityDenominator a.alpha (g (epsilon,x)) = actualShapeDenominator a epsilon x := by
        dsimp [g,actualShapeDenominator]
        rw [intrinsicComplexShape_eq,complexDensityDenominator_real_shape]
      rw [heq]
      intro hz
      rw [hz,norm_zero] at hgap
      have hp : 0 < c*(epsilon+‖x‖^2) := mul_pos hc (by positivity)
      linarith
    exact ((analyticAt_const.mul hh.1).div hh.2 hne).div_const
  have hmap : Continuous (fun p : ℂ × ShapeSpace n => (p.1,intrinsicComplexShape p.2)) :=
    continuous_fst.prodMk ((intrinsicComplexShape_continuous n).comp continuous_snd)
  obtain ⟨eta,heta,hTube⟩ := compact_analytic_parameter_domain (isCompact_closedBall (0:ShapeSpace n) R)
    (complexPostMeanResidue a.alpha) (fun p : ℂ × ShapeSpace n => (p.1,intrinsicComplexShape p.2))
    hmap (radialParameter a.theta epsilon) hbase
  refine ⟨eta,heta,?_⟩
  intro s hs x hx
  exact hTube s hs.le x (by simpa only [mem_closedBall,dist_zero_right] using hx)

end
end IsingBulk.First
