import IsingBulk.First.RegularShapeSource
import IsingBulk.First.RegularMeanJointAnalytic
import IsingBulk.First.ActualPostMeanLocalRegularity

/-! Fixed-cutoff integration of the actual regular-chart source.
Holomorphy, absolute integrability and every parameter interchange are proved
from the physical analytic neighborhood, before varying the radial parameter. -/
namespace IsingBulk.First.Regular
noncomputable section
open Complex MeasureTheory Filter Set Metric IsingBulk.Branch IsingBulk.First
open scoped Topology BigOperators

theorem complexPostMeanResidue_intrinsic {n : ℕ} (a : RegularChartData)
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I) = 1) (s : ℂ) (x : ShapeSpace n) :
    complexPostMeanResidue a.alpha (s,intrinsicComplexShape x) =
      postMeanDensity s a.alpha (intrinsicShapeCoordinates x)/((n+1).factorial:ℂ) := by
  rw [intrinsicComplexShape_eq]
  exact complexPostMeanResidue_real_shape s a.alpha _ ha

theorem actual_postMean_analytic_shape_tube {n : ℕ} (a : RegularChartData)
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

def localizedPostMeanDerivativeIntegral {n : ℕ} (a : RegularChartData) (k : ℕ)
    (chi : ShapeSpace n → ℂ) (epsilon : ℝ) : ℂ :=
  ∫ t : Fin n → ℝ, chi (shapeCoordinateEquiv n (WithLp.toLp 2 t))*
    (deriv^[k] (fun s => postMeanDensity s a.alpha t/((n+1).factorial:ℂ)))
      (radialParameter a.theta epsilon)

def intrinsicPostMeanIntegral {n : ℕ} (a : RegularChartData)
    (chi : ShapeSpace n → ℂ) (s : ℂ) : ℂ :=
  ∫ x : ShapeSpace n, chi x*(postMeanDensity s a.alpha (intrinsicShapeCoordinates x)/((n+1).factorial:ℂ))

def localizedPostMeanIntegral {n : ℕ} (a : RegularChartData)
    (chi : ShapeSpace n → ℂ) (s : ℂ) : ℂ :=
  ∫ t : Fin n → ℝ, chi (shapeCoordinateEquiv n (WithLp.toLp 2 t))*
    (postMeanDensity s a.alpha t/((n+1).factorial:ℂ))

theorem intrinsic_postMean_integral_interchange {n : ℕ} (a : RegularChartData)
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I) = 1)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I) = 1) :
    ∃ R : ℝ, 0 < R ∧ ∀ epsilon : ℝ, 0 < epsilon → epsilon < R →
      ∀ chi : ShapeSpace n → ℂ, Continuous chi → (∀ x, chi x ≠ 0 → ‖x‖ < R) →
      ∀ k : ℕ,
        (deriv^[k] (intrinsicPostMeanIntegral a chi)) (radialParameter a.theta epsilon) =
          ∫ x : ShapeSpace n, chi x*intrinsicPostMeanDerivative a k epsilon x := by
  obtain ⟨R,hR,hTube⟩ := actual_postMean_analytic_shape_tube (n := n) a hb
  refine ⟨R,hR,?_⟩
  intro epsilon he heR chi hchi hchis k
  obtain ⟨eta,heta,hT⟩ := hTube epsilon he heR
  let s₀ := radialParameter a.theta epsilon
  let K : Set (ShapeSpace n) := closedBall 0 R
  have hzero (x : ShapeSpace n) (hx : x ∉ K) : chi x = 0 := by
    by_contra hh
    exact hx (by simpa only [K,mem_closedBall,dist_zero_right] using (hchis x hh).le)
  have hF (s : ℂ) (hs : s ∈ ball s₀ eta) (x : ShapeSpace n) (hx : x ∈ K) :
      AnalyticAt ℂ (complexPostMeanResidue a.alpha) (s,intrinsicComplexShape x) := by
    apply hT s (by simpa only [mem_ball,dist_eq_norm,s₀] using hs) x
    simpa only [K,mem_closedBall,dist_zero_right] using hx
  have h := compact_analytic_shape_integral_iteratedDeriv (μ := (volume : Measure (ShapeSpace n)))
    (isCompact_closedBall (0:ShapeSpace n) R) isOpen_ball (complexPostMeanResidue a.alpha)
    intrinsicComplexShape (intrinsicComplexShape_continuous n) chi hchi hF k s₀ (mem_ball_self heta)
  have hfun : (fun s => ∫ x : ShapeSpace n in K, chi x*complexPostMeanResidue a.alpha (s,intrinsicComplexShape x)) =
      intrinsicPostMeanIntegral a chi := by
    funext s
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [hzero x hx,zero_mul])]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      rw [complexPostMeanResidue_intrinsic a ha]
  change (deriv^[k] (fun s => ∫ x : ShapeSpace n in K,
    chi x*complexPostMeanResidue a.alpha (s,intrinsicComplexShape x))) s₀ = _ at h
  rw [hfun] at h
  rw [h]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [hzero x hx,zero_mul])]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only
    have heq : (fun s => complexPostMeanResidue a.alpha (s,intrinsicComplexShape x)) =
        (fun s => postMeanDensity s a.alpha (intrinsicShapeCoordinates x)/((n+1).factorial:ℂ)) :=
      funext (fun s => complexPostMeanResidue_intrinsic a ha s x)
    rw [heq]
    rfl

theorem localizedPostMeanIntegral_eq_intrinsic {n : ℕ} (a : RegularChartData)
    (chi : ShapeSpace n → ℂ) (s : ℂ) :
    localizedPostMeanIntegral a chi s = (Real.sqrt (n+1))⁻¹ • intrinsicPostMeanIntegral a chi s := by
  simpa only [localizedPostMeanIntegral,intrinsicPostMeanIntegral,
    intrinsicShapeCoordinates_shapeCoordinateEquiv] using
    integral_shapeExtend n (fun x => chi x*(postMeanDensity s a.alpha (intrinsicShapeCoordinates x)/((n+1).factorial:ℂ)))

theorem actual_postMean_integral_interchange {n : ℕ} (a : RegularChartData)
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I) = 1)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I) = 1) :
    ∃ R : ℝ, 0 < R ∧ ∀ epsilon : ℝ, 0 < epsilon → epsilon < R →
      ∀ chi : ShapeSpace n → ℂ, Continuous chi → (∀ x, chi x ≠ 0 → ‖x‖ < R) →
      ∀ k : ℕ,
        (deriv^[k] (localizedPostMeanIntegral a chi)) (radialParameter a.theta epsilon) =
          localizedPostMeanDerivativeIntegral a k chi epsilon := by
  obtain ⟨R,hR,h⟩ := intrinsic_postMean_integral_interchange (n := n) a ha hb
  refine ⟨R,hR,?_⟩
  intro epsilon he heR chi hchi hchis k
  have hfun : localizedPostMeanIntegral a chi =
      fun s => ((Real.sqrt (n+1))⁻¹:ℂ)*intrinsicPostMeanIntegral a chi s := by
    funext s
    rw [localizedPostMeanIntegral_eq_intrinsic, Complex.real_smul, ofReal_inv]
  rw [hfun,iterate_deriv_const_mul]
  dsimp only
  rw [h epsilon he heR chi hchi hchis k]
  have hi := integral_shapeExtend n (fun x => chi x*intrinsicPostMeanDerivative a k epsilon x)
  simpa only [localizedPostMeanDerivativeIntegral,intrinsicPostMeanDerivative,
    intrinsicShapeCoordinates_shapeCoordinateEquiv,Complex.real_smul,ofReal_inv] using hi.symm

theorem actual_postMean_local_regularity {n : ℕ} (a : RegularChartData)
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I)=1)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I)=1) :
    ∃ R : ℝ, 0 < R ∧ ∀ epsilon : ℝ, 0 < epsilon → epsilon < R →
      ∀ chi : ShapeSpace n → ℂ, Continuous chi → (∀ x, chi x ≠ 0 → ‖x‖ < R) →
      AnalyticAt ℂ (intrinsicPostMeanIntegral a chi) (radialParameter a.theta epsilon) ∧
      ∃ eta : ℝ, 0 < eta ∧ ∀ s : ℂ, ‖s-radialParameter a.theta epsilon‖ < eta →
        Integrable (fun x : ShapeSpace n => chi x*
          (postMeanDensity s a.alpha (intrinsicShapeCoordinates x)/((n+1).factorial:ℂ))) := by
  obtain ⟨R,hR,hTube⟩ := actual_postMean_analytic_shape_tube (n := n) a hb
  refine ⟨R,hR,?_⟩
  intro epsilon he heR chi hchi hchis
  obtain ⟨eta,heta,hT⟩ := hTube epsilon he heR
  let s₀ := radialParameter a.theta epsilon
  let K : Set (ShapeSpace n) := closedBall 0 R
  have hzero (x : ShapeSpace n) (hx : x ∉ K) : chi x = 0 := by
    by_contra hh
    exact hx (by simpa only [K,mem_closedBall,dist_zero_right] using (hchis x hh).le)
  have hF (s : ℂ) (hs : s ∈ ball s₀ eta) (x : ShapeSpace n) (hx : x ∈ K) :
      AnalyticAt ℂ (complexPostMeanResidue a.alpha) (s,intrinsicComplexShape x) := by
    apply hT s (by simpa only [mem_ball,dist_eq_norm,s₀] using hs) x
    simpa only [K,mem_closedBall,dist_zero_right] using hx
  have hfun : (fun s => ∫ x : ShapeSpace n in K, chi x*complexPostMeanResidue a.alpha (s,intrinsicComplexShape x)) =
      intrinsicPostMeanIntegral a chi := by
    funext s
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [hzero x hx,zero_mul])]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only
      rw [complexPostMeanResidue_intrinsic a ha]
  constructor
  · have h := compact_analytic_shape_integral_analyticAt (μ := (volume : Measure (ShapeSpace n)))
      (isCompact_closedBall (0:ShapeSpace n) R) isOpen_ball (complexPostMeanResidue a.alpha)
      intrinsicComplexShape (intrinsicComplexShape_continuous n) chi hchi hF (mem_ball_self heta)
    change AnalyticAt ℂ (fun s => ∫ x : ShapeSpace n in K,
      chi x*complexPostMeanResidue a.alpha (s,intrinsicComplexShape x)) s₀ at h
    rwa [hfun] at h
  · refine ⟨eta,heta,?_⟩
    intro s hs
    apply integrable_of_continuousOn_compact_zero_compl (isCompact_closedBall (0:ShapeSpace n) R)
    · have hc : ContinuousOn (fun x : ShapeSpace n => complexPostMeanResidue a.alpha (s,intrinsicComplexShape x)) K := by
        intro x hx
        exact ((hF s (by simpa only [mem_ball,dist_eq_norm] using hs) x hx).continuousAt.comp
          (f := fun x : ShapeSpace n => (s,intrinsicComplexShape x))
          (continuous_const.prodMk (intrinsicComplexShape_continuous n)).continuousAt).continuousWithinAt
      simpa only [complexPostMeanResidue_intrinsic a ha] using! hchi.continuousOn.mul hc
    · intro x hx
      rw [hzero x hx,zero_mul]

end
end IsingBulk.First.Regular
