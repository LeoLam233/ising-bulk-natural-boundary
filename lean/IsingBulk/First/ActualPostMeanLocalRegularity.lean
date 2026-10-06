import IsingBulk.First.ActualPostMeanInterchange
import IsingBulk.First.CompactIntegralHolomorphic

/-! Actual local holomorphy and absolute shape integrability needed to
integrate and differentiate the source mean decomposition. -/
namespace IsingBulk.First
noncomputable section
open IsingBulk.Branch Complex MeasureTheory Set Filter Metric
open scoped Topology

theorem integrable_of_continuousOn_compact_zero_compl
    {X : Type*} [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasureOnCompacts μ] {K : Set X} (hK : IsCompact K)
    {F : X → ℂ} (hF : ContinuousOn F K) (hzero : ∀ x, x ∉ K → F x = 0) : Integrable F μ := by
  have hInd : K.indicator F = F := by
    funext x
    by_cases hx : x ∈ K
    · exact indicator_of_mem hx _
    · rw [indicator_of_notMem hx,hzero x hx]
  have hi : Integrable (K.indicator F) μ :=
    (hF.integrableOn_compact hK).integrable_indicator hK.measurableSet
  rwa [hInd] at hi

theorem actual_postMean_local_regularity {n : ℕ} (a : OrderedChartData)
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
end IsingBulk.First
