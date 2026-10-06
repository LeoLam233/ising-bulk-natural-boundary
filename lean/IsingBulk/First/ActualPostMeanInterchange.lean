import IsingBulk.First.ActualPostMeanAnalyticTube
import IsingBulk.First.CompactAnalyticShapeIntegral
import IsingBulk.First.ActualPostMeanCoordinateLimit

/-! Actual fixed-cutoff post-mean shape integration commutes with every
complex parameter derivative at each sufficiently close exterior radial point. -/
namespace IsingBulk.First
noncomputable section
open IsingBulk.Branch Complex MeasureTheory Set Filter Metric
open scoped Topology

def intrinsicPostMeanIntegral {n : ℕ} (a : OrderedChartData)
    (chi : ShapeSpace n → ℂ) (s : ℂ) : ℂ :=
  ∫ x : ShapeSpace n, chi x*(postMeanDensity s a.alpha (intrinsicShapeCoordinates x)/((n+1).factorial:ℂ))

def localizedPostMeanIntegral {n : ℕ} (a : OrderedChartData)
    (chi : ShapeSpace n → ℂ) (s : ℂ) : ℂ :=
  ∫ t : Fin n → ℝ, chi (shapeCoordinateEquiv n (WithLp.toLp 2 t))*
    (postMeanDensity s a.alpha t/((n+1).factorial:ℂ))

theorem intrinsic_postMean_integral_interchange {n : ℕ} (a : OrderedChartData)
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

theorem localizedPostMeanIntegral_eq_intrinsic {n : ℕ} (a : OrderedChartData)
    (chi : ShapeSpace n → ℂ) (s : ℂ) :
    localizedPostMeanIntegral a chi s = (Real.sqrt (n+1))⁻¹ • intrinsicPostMeanIntegral a chi s := by
  simpa only [localizedPostMeanIntegral,intrinsicPostMeanIntegral,
    intrinsicShapeCoordinates_shapeCoordinateEquiv] using
    integral_shapeExtend n (fun x => chi x*(postMeanDensity s a.alpha (intrinsicShapeCoordinates x)/((n+1).factorial:ℂ)))

theorem actual_postMean_integral_interchange {n : ℕ} (a : OrderedChartData)
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

end
end IsingBulk.First
