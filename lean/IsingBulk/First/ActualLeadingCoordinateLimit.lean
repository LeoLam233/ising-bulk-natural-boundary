import IsingBulk.First.ActualLeadingShapeLimit
import IsingBulk.First.FirstCoefficient

/-! Exact source free-coordinate measure and 2π normalization of the actual
highest-pole shape asymptotic. -/
namespace IsingBulk.First
noncomputable section
open IsingBulk.Branch Complex MeasureTheory Filter
open scoped Topology

@[simp] theorem intrinsicShapeCoordinates_shapeCoordinateEquiv {n : ℕ} (t : Fin n → ℝ) :
    intrinsicShapeCoordinates (shapeCoordinateEquiv n (WithLp.toLp 2 t)) = t := by
  funext j
  exact shapeExtend_castSucc t j

/-- The actual highest pole, including 2π and 1/N!, in the source's n free
shape coordinates. No radius parameter remains in this density. -/
def actualLeadingShapeDensity {n : ℕ} (a : OrderedChartData) (k : ℕ) (epsilon : ℝ)
    (t : Fin n → ℝ) : ℂ :=
  2*(Real.pi:ℂ)*(firstVandermonde (shapeExtend t):ℂ)^2 *
    actualLeadingAmplitude a n k (radialParameter a.theta epsilon,t) /
    (shapePoleDenominator (radialParameter a.theta epsilon) a.alpha t)^(k+1)

theorem actual_leading_coordinate_sqrt_limit {n k : ℕ} (hn : 1 ≤ n)
    (hdegree : n-1+(n+1)*n = 2*k) (a : OrderedChartData) (he : Even (n+1))
    (ha : exp (-(n+1:ℂ)*(a.alpha:ℂ)*I) = 1)
    (hb : exp (-(n+1:ℂ)*(a.beta:ℂ)*I) = 1) :
    ∃ R : ℝ, 0 < R ∧ ∀ chi : ShapeSpace n → ℂ,
      Continuous chi → chi 0 = 1 → (∀ x, ‖chi x‖ ≤ 1) →
      (∀ x, chi x ≠ 0 → ‖x‖ < R) →
      Tendsto (fun epsilon : ℝ => Real.sqrt epsilon • ∫ t : Fin n → ℝ,
        chi (shapeCoordinateEquiv n (WithLp.toLp 2 t))*actualLeadingShapeDensity a k epsilon t)
        (𝓝[>] 0) (𝓝 (localLeadingCoefficient a n k)) := by
  obtain ⟨R,hR,h⟩ := actual_leading_shape_sqrt_limit hn hdegree a he ha hb
  refine ⟨R,hR,?_⟩
  intro chi hchi hchi0 hchib hchis
  have ht := ((h chi hchi hchi0 hchib hchis).const_mul (2*(Real.pi:ℂ))).const_smul (Real.sqrt (n+1))⁻¹
  convert ht using 1
  · funext epsilon
    have hi := integral_shapeExtend n (fun x => (shapeVandermondeSq x:ℂ)*chi x*
      intrinsicLeadingAmplitude a k (epsilon,x)/(actualShapeDenominator a epsilon x)^(k+1))
    have heq : (∫ t : Fin n → ℝ,
        chi (shapeCoordinateEquiv n (WithLp.toLp 2 t))*actualLeadingShapeDensity a k epsilon t) =
        2*(Real.pi:ℂ)*∫ t : Fin n → ℝ,
          let x := shapeCoordinateEquiv n (WithLp.toLp 2 t)
          (shapeVandermondeSq x:ℂ)*chi x*intrinsicLeadingAmplitude a k (epsilon,x)/
            (actualShapeDenominator a epsilon x)^(k+1) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun t => by
        simp only [actualLeadingShapeDensity, intrinsicLeadingAmplitude, intrinsicRadialEmbedding,
          actualShapeDenominator, intrinsicShapeCoordinates_shapeCoordinateEquiv,
          shapeVandermondeSq, shapeCoordinateEquiv_apply, ofReal_pow]
        ring
    rw [heq, hi]
    simp only [Complex.real_smul]
    ring
  · congr 1
    rw [localLeadingCoefficient, shapePeriod_eq_intrinsic]
    simp only [Complex.real_smul, ofReal_mul, ofReal_ofNat]
    ring

end
end IsingBulk.First
